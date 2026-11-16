#!/usr/bin/env python3
"""FUZZ10: random differential tests of the newest compiled entries (NOTES sections 26, 28, 29, 32 and the harvest entries
with plain / `wa` work bounds) against EXECUTED Lean (`ref10.lean`: the same `f` the emitters apply, run by `lake env lean`) and
the machine code (QEMU, or Sail for a sample). Harness machinery as in Testing/asm/fuzz6/fuzz6.py (FUZZ6).
usage: fuzz10.py FN SEED NCASES [qemu|sail] [big]     env: FILL, SAILMAX (sail input bytes), BIG=1, CORRUPT=1, SHORT=k
Per case: [G in G][out R G][G work WK G] with G = 16 guard bytes, output pre-filled random, work block random-filled and exactly the
bound the .words header states: plain `N` -> 8 (N + 1) + 7, `wa A N B L` -> 8 (A + B n) + 8 (N + 1) + 7 (n = input bytes).
Checks: output == Lean; input / guards on both sides of input, output and work; gp / sp restored; a1 = result length when the header
says so; QEMU: the memory image outside output + work blocks is unchanged (two random fills; a byte is written iff it differs from its
fill in either run); Sail: every memory write lies in an output or work block (trace filtered to `mem[W` lines)."""
import os, random, re, subprocess, sys, threading, bisect
import numpy as np
threading.stack_size(1 << 27)
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.join(D, "..", "..", "..")
WD = os.path.join(ROOT, "Testing", "asm", "frontx-words")
W = os.path.join(D, "work" + os.environ.get("WSUF", "")); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
M64 = 2 ** 64; G = 16; E = 72
sh = lambda c: subprocess.run(c, shell=True, check=True)
le = lambda x, k=8: (x % 2 ** (8 * k)).to_bytes(k, "little")
EDGE = [0, 1, 2, 3, 4, 5, 7, 8, 15, 16, 31, 32, 127, 128, 255, 256, 65535, 65536, 2 ** 31 - 1, 2 ** 31, 2 ** 32 - 1, 2 ** 32, 2 ** 63 - 1, 2 ** 63,
        2 ** 63 + 1, M64 - 2, M64 - 1, M64 - 256, 2 ** 64 - 2 ** 32]
INT_EDGE = [0, 1, -1, 2, -2, 255, -256, 2 ** 31 - 1, -2 ** 31, 2 ** 31, 2 ** 32 - 1, -2 ** 32, 2 ** 53 + 1, 2 ** 63 - 1, -2 ** 63, -2 ** 63 + 1, 2 ** 63 - 2, 1000000007, -999999999]
# ---------------- input generators per family (the Lean reference executes the entry on these bytes)
def r64(r):
    k = r.random()
    if k < .45: return r.choice(INT_EDGE) % M64
    if k < .8: return r.randrange(M64)
    return r.randrange(-300, 300) % M64
def gen_int(r, L):
    """8-byte little-endian two's-complement words (edge and random), cut to L bytes (a short input is zero-extended by the entry)"""
    return b"".join(le(r64(r)) for _ in range(-(-L // 8)))[:L]
def gen_st(r, L):
    """structure bytes: flags, RGBA-like, and PNG-like header fields (pool of 0, 0xFF, 0x80, small flag bits, random bytes)"""
    pool = [0, 0xFF, 0x80, 0x7F, 0x01, 0x20, 0x10, 0x40, 0x04, 0x08]
    return bytes(r.choice(pool) if r.random() < .6 else r.getrandbits(8) for _ in range(L))
def gen_wa3(r, L):
    """index bytes for `entryAt` / `lenAt` / `symAt` (index = xs[0] + xs[1], table of 256 entries): edge bytes, sums past 255"""
    return bytes(r.choice([0, 1, 127, 128, 254, 255]) if r.random() < .5 else r.getrandbits(8) for _ in range(L))
def gen_mon(r, L):
    """list-of-bytes inputs: runs of 0 / 1 / 3 / 32 / 255 / 0xC3 (UTF-8 lead byte) and random bytes"""
    pool = [0, 1, 3, 4, 5, 31, 32, 33, 127, 255, 0xC3]
    return bytes(r.choice(pool) if r.random() < .6 else r.getrandbits(8) for _ in range(L))
def gen_mix(r):
    """mixHash: 16 bytes (h, k), edge pairs and random pairs"""
    return b"".join(le(r64(r)) for _ in range(2))
FAM = {"int": gen_int, "wa_int": gen_int, "st": gen_st, "wa3": gen_wa3, "mon": gen_mon}
ENTRIES = {}
for n in ["int_clamp", "int_inrange", "int_ofnat", "int_mul", "int_floor", "int_ceil", "int_round", "int_abs", "int_min", "int_max", "int_scale16",
          "int_clamplin", "int_lininrange", "int_clampix", "int_round32", "int_fitsi16", "int_insidew", "int_norm2", "int_clampto", "int_morphceil"]:
    ENTRIES[n] = "int"
for n in ["wa_int_iops", "wa_int_icmp", "wa_int_fxrounds", "wa_int_sumdev"]: ENTRIES[n] = "wa_int"
for n in ["rgba", "hdr", "rgbag", "interlace", "canvash", "compoundvalid", "setlig", "lignumcomps", "isignorable", "rgbahdr"]: ENTRIES["st_" + n] = "st"
for n in ["entryat", "lenat", "symat"]: ENTRIES["wa_" + n] = "wa3"
for n in ["countgt3", "countnotgt3", "countgt3exc", "sumnze", "countzerose", "countabovere", "maxste", "splite", "firstbige", "trysube", "desfindgt3",
          "loopfindgt3", "contfindgt3", "loopcountsp", "twoe", "threee", "sixe"]: ENTRIES["mon_" + n] = "mon"
ENTRIES["wa_mixhash"] = "mix"
# ---------------- work bounds from the .words header
def hdr(fn): return open(f"{WD}/{fn}.words").readline().split()
def work_of(h, n):
    if h[0] == "wa": return 8 * (int(h[1]) + int(h[3]) * n) + 8 * (int(h[2]) + 1) + 7
    if h[0].isdigit(): return 8 * (int(h[0]) + 1) + 7
    raise ValueError(f"header kind {h[0]} not handled by FUZZ10")
# ---------------- Lean reference (executed)
PANICS = {}
def lean_results(fn, ins):
    open(f"{W}/{fn}.in", "w").write("".join(f"{fn} {x.hex() or '-'}\n" for x in ins))
    env = dict(os.environ, FZ_IN=f"{W}/{fn}.in", FZ_OUT=f"{W}/{fn}.out")
    p = subprocess.run("ulimit -s unlimited; lake env lean Testing/asm/fuzz10/ref10.lean", shell=True, cwd=ROOT, env=env, capture_output=True, text=True, executable="/bin/bash")
    # a PANIC is Lean's `get!`-style default on an input shorter than the entry reads (same default as the committed .cases): kept, counted
    assert p.returncode == 0 and "error" not in p.stdout + p.stderr, (p.stdout + p.stderr)[-2000:]
    PANICS[fn] = PANICS.get(fn, 0) + (p.stdout + p.stderr).count("PANIC at")
    outs = open(f"{W}/{fn}.out").read().split("\n")[:-1]; assert len(outs) == len(ins), (fn, len(outs), len(ins))
    os.remove(f"{W}/{fn}.in"); os.remove(f"{W}/{fn}.out")
    return [b"" if o == "-" else bytes.fromhex(o) for o in outs]
# ---------------- machine (as FUZZ6)
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
DRIVER = """.section .text.start
.globl _start
_start: lla s0, tab
  li s2, %d
1: ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  ld sp, 32(s0)
  ld gp, 40(s0)
  jal ra, func
  sd gp, 48(s0)
  sd sp, 56(s0)
  sd a1, 64(s0)
  addi s0, s0, %d
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
func:
%s.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
"""
MAGIC = 0x0123456789ABCDEF
def build(fn, cases, wks, fill, tag):
    rf = random.Random(f"fill{fill}"); words = [int(l, 16) for l in open(f"{WD}/{fn}.words").read().split("\n")[1:] if l.strip()]
    data = bytearray(); tab = []; lay = []
    for (xs, ys), WK in zip(cases, wks):
        n, R = len(xs), len(ys)
        i0 = len(data) + G; o0 = i0 + n + G; w0 = (o0 + R + G + G + 7) // 8 * 8
        lay.append((i0, o0, w0, WK, n, R))
        data += b"\xAA" * G + xs + b"\xAA" * G + rf.randbytes(R) + b"\xAA" * G
        data += b"\xAA" * (w0 - len(data) - G) + b"\xAA" * G + rf.randbytes(WK) + b"\xAA" * G
        tab.append((i0, n, w0, o0, w0 + WK))
    open(f"{W}/{tag}.bin", "wb").write(data)
    func = "".join(f"  .word 0x{w:08x}\n" for w in words)
    ent = "\n".join(f"  .quad base+{a}, {b}, base+{c}, base+{d}, base+{e}, {MAGIC}, 0, 0, 0" for a, b, c, d, e in tab)
    open(f"{W}/{tag}.S", "w").write(DRIVER % (len(cases), E, func) + f'.data\n.align 4\nbase:\n.incbin "{W}/{tag}.bin"\n.align 3\ntab:\n{ent}\n')
    open(f"{W}/m.ld", "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{W}/m.ld -Wl,--no-relax -Wl,--build-id=none {W}/{tag}.S -o {W}/{tag}.elf")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {W}/{tag}.elf", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    return lay, sym("halt"), sym("base"), sym("tab"), len(data), bytes(data)
def qemu(tag, halt, a, n):
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 3G -bios {W}/{tag}.elf -display none -serial none -monitor stdio",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version")
    while "pc       %016x" % halt not in hmp("info registers"): pass
    hmp(f'pmemsave {a:#x} {n} "{W}/{tag}.q"'); q.stdin.write("quit\n"); q.wait()
    d = open(f"{W}/{tag}.q", "rb").read(); os.remove(f"{W}/{tag}.q"); return d
def check_batch(fn, cases, wks, retlen, fill, target, stats):
    tag = f"{fn}_{target}"
    lay, halt, base, tab, size, init = build(fn, cases, wks, fill, tag)
    if target == "qemu":
        lay2, _, _, _, _, init2 = build(fn, cases, wks, fill + 1000, tag + "b")
        mems = [(qemu(tag, halt, base, tab + E * len(cases) - base), init), (qemu(tag + "b", halt, base, tab + E * len(cases) - base), init2)]
    else:
        subprocess.run(f"{SAIL} --inst-limit 4000000000 --trace-mem --trace-output /dev/stdout {W}/{tag}.elf 2>&1 | grep -aE 'mem\\[W|SUCCESS|FAIL|limit' > {W}/{tag}.log",
                       shell=True, executable="/bin/bash")
        iv = [(tab, tab + E * len(cases))]
        for (i0, o0, w0, WK, n, R) in lay: iv += [(base + o0, base + o0 + R), (base + w0, base + w0 + WK)]
        iv.sort(); los = [a for a, _ in iv]
        def okaddr(a):
            j = bisect.bisect_right(los, a) - 1
            return j >= 0 and a < iv[j][1]
        smem = bytearray(init) + bytearray(b"\0" * (E * len(cases) + tab - base - size))
        seen = False
        for l in open(f"{W}/{tag}.log", errors="replace"):
            if "SUCCESS" in l: seen = True
            m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
            if not m: continue
            a, v = int(m.group(1), 16), m.group(2)
            if a < base: continue
            nb = len(v) // 2
            for j in range(nb):
                assert okaddr(a + j), f"unexpected Sail write {l.strip()} ({fn})"
                smem[a + j - base] = int(v[2 * (nb - 1 - j):2 * (nb - j)], 16)
        os.remove(f"{W}/{tag}.log"); assert seen, "Sail: no SUCCESS"
        mems = [(bytes(smem), init)]
    for mem, ini in mems[:1] if target != "qemu" else mems:
        for c, ((xs, ys), (i0, o0, w0, WK, n, R)) in enumerate(zip(cases, lay)):
            got = bytes(mem[o0:o0 + R])
            assert got == ys, (target, fn, "OUTPUT", n, got[:64].hex(), ys[:64].hex(), "reproducer", xs.hex() if n < 400 else f"len {n}")
            assert mem[i0 - G:i0 + n + G] == b"\xAA" * G + xs + b"\xAA" * G, (target, fn, "input/guard", n)
            assert mem[o0 + R:o0 + R + G] == b"\xAA" * G, (target, fn, "output guard", n)
            assert mem[w0 - G:w0] == b"\xAA" * G and mem[w0 + WK:w0 + WK + G] == b"\xAA" * G, (target, fn, "work guard", n, xs.hex() if n < 400 else f"len {n}")
            e = tab - base + E * c
            gp, spo, a1 = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56, 64))
            assert gp == MAGIC and spo == base + w0 + WK, (target, fn, "gp/sp", n)
            if retlen: assert a1 == R, (target, fn, "a1", n, a1, R)
        prev = 0
        for (i0, o0, w0, WK, n, R) in lay:
            for lo, hi in ((prev, o0), (o0 + R, w0)):
                assert mem[lo:hi] == ini[lo:hi], (target, fn, "memory outside output/work changed", lo, hi)
            prev = w0 + WK
        assert mem[prev:len(ini)] == ini[prev:len(ini)], (target, fn, "tail changed")
    if target == "qemu":
        (m1, i1), (m2, i2) = mems
        for (i0, o0, w0, WK, n, R), (xs, ys) in zip(lay, cases):
            x1 = np.frombuffer(m1, np.uint8, WK, w0); y1 = np.frombuffer(i1, np.uint8, WK, w0)
            x2 = np.frombuffer(m2, np.uint8, WK, w0); y2 = np.frombuffer(i2, np.uint8, WK, w0)
            wr = (x1 != y1) | (x2 != y2)
            idx = np.flatnonzero(wr); edges = np.concatenate(([-1], idx, [WK]))
            runs = np.diff(edges) - 1; best = int(runs.max())
            stats.append((n, WK, best, int(wr.sum()), fn))
def run_batches(fn, cases, wks, retlen, fill, target, stats):
    """one QEMU image per batch of at most 250 MB (cases are never split)"""
    batch, bw, tot, nb = [], [], 0, 0
    def flush(batch, bw):
        nonlocal nb
        if batch: check_batch(fn, batch, bw, retlen, fill + nb, target, stats); nb += 1
    for c, wk in zip(cases, wks):
        sz = len(c[0]) + wk + len(c[1]) + 100
        if tot + sz > 250 * 2 ** 20: flush(batch, bw); batch, bw, tot = [], [], 0
        batch.append(c); bw.append(wk); tot += sz
    flush(batch, bw)
def gen_cases(fn, seed, N, big):
    r = random.Random(f"{fn}/{seed}")
    sizes = [0, 1, 2, 3, 4, 7, 8, 9, 16] + [r.randrange(0, 60) for _ in range(N)]
    sizes = sizes[:N]
    if big: sizes += [0, 30000, 100000] if ENTRIES[fn] in ("mon", "st") else [0, 16, 40] if ENTRIES[fn] in ("int", "wa_int") else [0, 1, 8]
    return [make_input(fn, r, s) for s in sizes]
def make_input(fn, r, s):
    f = ENTRIES[fn]
    if f == "mix": return b"".join(le(r64(r)) for _ in range(2))
    return FAM[f](r, s if f != "wa3" else min(s, 8))
def main():
    fn, seed, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); target = sys.argv[4] if len(sys.argv) > 4 else "qemu"
    big = len(sys.argv) > 5 or os.environ.get("BIG") == "1"
    h = hdr(fn); retlen = (h[0] == "wa" and h[4] == "1")
    ins = gen_cases(fn, seed, N, big)
    if target == "sail":
        mx = int(os.environ.get("SAILMAX", "1500")); ins = [x for x in ins if len(x) <= mx]
    outs = lean_results(fn, ins)
    if os.environ.get("CORRUPT"): outs[-1] = bytes([outs[-1][0] ^ 1]) + outs[-1][1:] if outs[-1] else b"\x01"
    cases = list(zip(ins, outs))
    wks = [work_of(h, len(x)) - int(os.environ.get("SHORT", 0)) for x in ins]
    stats = []; run_batches(fn, cases, wks, retlen, int(os.environ.get("FILL", seed)), target, stats)
    ex = f"; heap/stack gap min {min(s[2] for s in stats)} B, max written fraction {max(s[3] / s[1] for s in stats):.3f}" if stats and target == "qemu" else ""
    pn = PANICS.get(fn, 0)
    print(f"{fn}: {len(cases)} cases ok on {target} (seed {seed}; max input {max(len(c[0]) for c in cases)} B, max out {max(len(c[1]) for c in cases)} B, max work {max(wks)} B{ex}; Lean PANIC (default value on short input) x{pn})")
    if os.environ.get("DUMP_STATS"): open(os.environ["DUMP_STATS"], "w").write(repr(stats))
    sys.stdout.flush()
err = []
def run():
    try: main()
    except BaseException as e:
        import traceback; err.append(traceback.format_exc()); print("FAIL", sys.argv[1], repr(e)[:2000]); print(err[-1][-1500:])
if __name__ == "__main__":
    t = threading.Thread(target=run); t.start(); t.join()
    sys.exit(1 if err else 0)
