#!/usr/bin/env python3
"""FUZZ9: random differential tests of the con-leche `Expr` entries (NOTES section 25), the higher-order entries (section 27) and the
TinyRepro entries r1-r5, against executed Lean (`gen9.lean`: the repo's own functions and encoders).
usage: fuzz9.py ENTRY SEED N [qemu|sail] [big]    env: FILL, SAILMAX (max input bytes for sail), SHORT=k (harness sanity)
Work block per case: exactly the stated bound (`indw`: Ind.spaceA m nl cells n with the model's cells for this input; plain: 8 (slots + 1) + 7).
Checks as in fuzz6: output == Lean, a1 == result length (retLen entries), gp/sp, guards, QEMU: no byte outside output + work + result slots changes
(two fills; heap/stack gap > 0), Sail: every `mem[W` write lies in output or work block."""
import os, random, re, subprocess, sys, threading
import numpy as np
sys.setrecursionlimit(10 ** 7); threading.stack_size(1 << 30)
D = os.path.dirname(os.path.abspath(__file__)); WD = os.path.join(D, "..", "frontx-words"); WD2 = os.path.join(D, "words")
W = os.path.join(D, "work" + os.environ.get("WSUF", "")); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
M64 = 2 ** 64; G = 16; E = 72
sh = lambda c: subprocess.run(c, shell=True, check=True)
def spaceA(m, nl, cells, n):
    wn = 8 + 4 * n + 4 * cells
    return 8 * wn + 56 + 8 * (nl + 1) * (n + m * (1 + wn)) + 24
BUDGET = lambda: int(os.environ.get("BUDGET", 250)) * 2 ** 20
def run_batches(fn, cases, wks, retlen, fill, target, stats, quiet=False):
    """check_batch over batches whose images stay below BUDGET bytes; the stats are in case order"""
    batch = []; bw = []; tot = 0; nb = 0
    def flush():
        nonlocal batch, bw, tot, nb
        if batch: check_batch(fn, batch, bw, retlen, fill + nb, target, stats, quiet); nb += 1
        batch = []; bw = []; tot = 0
    for c, wk in zip(cases, wks):
        sz = len(c[0]) + wk + len(c[1]) + 100
        if tot + sz > BUDGET(): flush()
        batch.append(c); bw.append(wk); tot += sz
    flush()
# ---------------- machine
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
    rf = random.Random(f"fill{fill}"); words = [int(l, 16) for l in open(wfile(fn)).read().split("\n")[1:] if l.strip()]
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
def check_batch(fn, cases, wks, retlen, fill, target, stats, quiet=False):
    tag = f"{fn}_{target}"
    lay, halt, base, tab, size, init = build(fn, cases, wks, fill, tag)
    if target == "qemu":
        lay2, _, _, _, _, init2 = build(fn, cases, wks, fill + 1000, tag + "b")
        mems = [(qemu(tag, halt, base, tab + E * len(cases) - base), init), (qemu(tag + "b", halt, base, tab + E * len(cases) - base), init2)]
    else:
        # only the memory-write lines of the trace are kept (a full fetch trace would fill the disk)
        subprocess.run(f"{SAIL} --inst-limit 4000000000 --trace-mem --trace-output /dev/stdout {W}/{tag}.elf 2>&1 | grep -aE 'mem\\[W|SUCCESS|FAIL|limit' > {W}/{tag}.log",
                       shell=True, executable="/bin/bash")
        import bisect
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
    for mi, (mem, ini) in enumerate(mems):
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
            # a byte is "written" iff its final value differs from its initial fill in either run (it can only be missed if the program
            # wrote exactly the old fill byte in both runs: 2^-16); the gap is the longest never-written run: heap grows up, stack down
            x1 = np.frombuffer(m1, np.uint8, WK, w0); y1 = np.frombuffer(i1, np.uint8, WK, w0)
            x2 = np.frombuffer(m2, np.uint8, WK, w0); y2 = np.frombuffer(i2, np.uint8, WK, w0)
            wr = (x1 != y1) | (x2 != y2)
            idx = np.flatnonzero(wr); edges = np.concatenate(([-1], idx, [WK]))       # unwritten runs lie between consecutive written bytes
            runs = np.diff(edges) - 1; j = int(np.argmax(runs)); best = int(runs[j]); bs = int(edges[j] + 1)
            stats.append((n, WK, best, int(wr.sum()), bs, fn))
            assert quiet or best > 0 or WK < 64, (target, fn, "no slack: heap and stack may have met", n)

wfile = lambda fn: f"{WD2}/{fn}.words" if os.path.exists(f"{WD2}/{fn}.words") else f"{WD}/{fn}.words"
MN = {"expr_inst1": (1, 19)}   # (functions, locals) of the entry's theorem `Ind.spaceA m nl`; default (1, 16); tinyr: from words header
def hdr(fn): return open(wfile(fn)).read().split("\n")[0].split()
def work_of(fn, h, n, cells):
    if h[0] == "indw":
        m, nl = (int(h[2]), int(h[3])) if len(h) > 2 else MN.get(fn, (1, 16))
        return spaceA(m, nl, cells, n)
    return 8 * (int(h[0]) + 1) + 7
def gen_lines(fn, seed, N, big):
    p = subprocess.run(f"export PATH=$HOME/.elan/bin:$PATH; ulimit -s unlimited; cd {D}/../../..; G9='{fn[5:] if fn.startswith('expr_') else fn} {seed} {N}{' big' if big else ''}' lake env lean --tstack=16000000 Testing/asm/fuzz9/gen9.lean",
                       shell=True, capture_output=True, text=True, executable="/bin/bash")
    assert p.returncode == 0, p.stderr[-2000:]
    out = []
    for l in p.stdout.split("\n"):
        if not l.strip(): continue
        if not re.fullmatch(r"[0-9a-f-]+ [0-9a-f-]+ \d+", l): continue
        x, y, c = l.split(); out.append((bytes.fromhex(x) if x != "-" else b"", bytes.fromhex(y) if y != "-" else b"", int(c)))
    assert len(out) == N, (len(out), p.stderr[-500:]); return out
def main():
    fn, seed, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); target = sys.argv[4] if len(sys.argv) > 4 else "qemu"
    big = len(sys.argv) > 5 or os.environ.get("BIG") == "1"
    h = hdr(fn); retlen = h[0] == "indw" and h[1] == "1"
    vals = gen_lines(fn, seed, N, big)
    if target == "sail":
        mx = int(os.environ.get("SAILMAX", "2000")); vals = [v for v in vals if len(v[0]) <= mx]
    cases = [(v[0], v[1]) for v in vals]
    if os.environ.get("CORRUPT"): cases[-1] = (cases[-1][0], bytes([cases[-1][1][0] ^ 1]) + cases[-1][1][1:])
    wks = [work_of(fn, h, len(v[0]), v[2]) - int(os.environ.get("SHORT", 0)) for v in vals]
    stats = []; run_batches(fn, cases, wks, retlen, int(os.environ.get("FILL", seed)), target, stats)
    ex = f"; heap/stack gap min {min(s[2] for s in stats)} B, min gap/block {min(s[2] / s[1] for s in stats):.3f}, max written fraction {max(s[3] / s[1] for s in stats):.3f}" if stats else ""
    print(f"{fn}: {len(cases)} cases ok on {target} (seed {seed}; max input {max(len(c[0]) for c in cases)} B, max out {max(len(c[1]) for c in cases)} B, max work {max(wks)} B{ex})")
    if os.environ.get("DUMP_STATS"): open(os.environ["DUMP_STATS"], "w").write(repr(stats))
err = []
def run():
    try: main()
    except BaseException as e:
        import traceback; err.append(traceback.format_exc()); print("FAIL", sys.argv[1], repr(e)[:2000]); print(err[-1][-1500:])
if __name__ == "__main__":
    t = threading.Thread(target=run); t.start(); t.join()
    sys.exit(1 if err else 0)
