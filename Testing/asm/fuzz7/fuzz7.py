#!/usr/bin/env python3
"""FUZZ7: differential tests of the multiply/divide/remainder/shift-by-variable entries (NOTES section 22) against executed Lean
(`ref.lean`, verbatim source functions) and an independent Python reference.
usage: fuzz7.py FN SEED NCASES qemu|sail     FN in FNS below (words and header from ../frontx-words/FN.words)
Per case: [G in G][out R G][pad][G work WK G]; output pre-filled with random bytes, work block random-filled, WK = the stated
work size exactly.  QEMU runs twice (fill A, then its complement); checks per run: output == Lean == Python; a1 == R for list
results; gp, sp restored; every guard; the whole memory image outside output + work + result slots equals the initial image.
Across the two runs: the output is the same (no read of uninitialised memory); the bytes equal in both final work blocks are
the written ones (the complement fill differs everywhere), the longest never-written run must be > 0 (heap and stack did not meet).
Sail: only `mem[W` lines are kept (grep in the pipe); every write must lie in output + work block + result slots (or be tohost)."""
import math, os, random, re, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); WD = os.path.join(D, "..", "frontx-words")
W = os.path.join(D, "work" + os.environ.get("WSUF", "")); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
LEAN = os.popen("ls -d /tmp/leandl/x/*/bin").read().split()[0] + "/lean"
M64 = 2 ** 64; G = 16; E = 72; MAGIC = 0x0123456789ABCDEF
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
le = lambda x, n=8: (x % 2 ** (8 * n)).to_bytes(n, "little")
rdn = lambda xs, o, n: sum((xs[o + j] if o + j < len(xs) else 0) << (8 * j) for j in range(n))

def ops(a, b, w, sh_):
    M = 2 ** 64 if w is None else 2 ** w
    q = a // b if b else 0; r = a % b if b else a
    s = b % sh_
    hi = a >> b if w is None else a >> s
    return ((a * b) ^ q ^ r ^ (a << s) ^ hi) % M
def hist(xs):
    c = [0] * 16
    for x in xs:
        if 0 < x <= 15: c[x] += 1
    return c
def nextcodes(xs):
    c = hist(xs); nc = [0] * 16; code = 0
    for bits in range(1, 16):
        code = (code + c[bits - 1]) * 2; nc[bits] = code % 2 ** 32
    return b"".join(le(v, 4) for v in nc)
# name -> python reference (bytes)
PY = {
    "wa_kraft": lambda xs: le(sum(n << (15 - b) for b, n in enumerate(hist(xs)) if b)),
    "wa_nextcodes": nextcodes,
    "wa_gcd": lambda xs: le(math.gcd(rdn(xs, 0, 4), rdn(xs, 4, 4))),
    "fx_gcd": lambda xs: le(math.gcd(rdn(xs, 0, 8), rdn(xs, 8, 8))),
    "wa_ops64": lambda xs: le(ops(rdn(xs, 0, 8), rdn(xs, 8, 8), 64, 64)),
    "fx_ops64": lambda xs: le(ops(rdn(xs, 0, 8), rdn(xs, 8, 8), 64, 64)),
    "wa_ops32": lambda xs: le(ops(rdn(xs, 0, 4), rdn(xs, 4, 4), 32, 32), 4),
    "fx_ops32": lambda xs: le(ops(rdn(xs, 0, 4), rdn(xs, 8, 4), 32, 32), 4),
    "wa_opsn": lambda xs: le(ops(rdn(xs, 0, 4), rdn(xs, 4, 4), None, 64)),
    "fx_opsn": lambda xs: le(ops(rdn(xs, 0, 8), rdn(xs, 8, 8), None, 64)),
}
LISTS = {"wa_nextcodes"}                     # a1 = result length
FNS = list(PY)

# ---------- inputs
A64 = [0, 1, 2, 3, 5, 255, 256, 2**31 - 1, 2**31, 2**31 + 1, 2**32 - 2, 2**32 - 1, 2**32, 2**32 + 1, 2**32 + 5, 2**48,
       2**62, 2**63 - 1, 2**63, 2**63 + 1, M64 - 2, M64 - 1, 0xFFFFFFFF00000000, 0x1FFFFFFFF, 0x8000000080000000,
       0xDEADBEEFCAFEBABE, 0xFFFF0000, 0x10000, 0x7FFFFFFF7FFFFFFF]
B64 = [0, 1, 2, 3, 7, 2**31, 2**32 - 1, 2**32, 2**32 + 1, 2**63, 2**63 + 1, M64 - 2, M64 - 1] + list(range(0, 131))
def fib(n):
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a
def pairs(r, bits, n):
    m = 2 ** bits
    out = [(a % m, b % m) for a in A64 for b in B64[:13] + [0, 1, 31, 32, 33, 63, 64, 65, 127, 128]]    # edge x edge
    out += [(a % m, b) for a in (0, 1, 5, 2**31 + 3, 2**32 - 1, 0xDEADBEEFCAFEBABE % m, m - 1) for b in range(131)]  # shift amounts 0..130
    out += [(fib(k) % m, fib(k + 1) % m) for k in range(1, 95)] + [(fib(k + 1) % m, fib(k) % m) for k in range(1, 95)]
    while len(out) < n:
        k = r.random()
        pick = lambda: r.choice(A64) % m if r.random() < .4 else r.randrange(m) if r.random() < .6 else r.randrange(m) >> r.randrange(bits)
        out.append((pick(), pick() if k < .7 else r.choice(B64) % m if k < .85 else r.randrange(1, 300)))
    r.shuffle(out); return out
def scal_inputs(fn, r, n):
    """scalar entries: 16 bytes (fx: two 64-bit words; wa_ops64) or 8 bytes (wa 32-bit words); a few short / long inputs"""
    bits = 32 if fn in ("wa_gcd", "wa_ops32", "wa_opsn") else 64
    nb = bits // 8
    xs = []
    for a, b in pairs(r, bits, n):
        k = r.random()
        if fn == "fx_ops32" and r.random() < .5:       # garbage in the high halves: the operands are masked
            a += r.randrange(2**32) << 32; b += r.randrange(2**32) << 32
        x = le(a, 8 if bits == 64 or fn == "fx_ops32" else 4) + le(b, 8 if bits == 64 or fn == "fx_ops32" else 4)
        if k < .03: x = x[:r.randrange(len(x))]                     # short input: the missing bytes read as 0
        elif k < .06: x += bytes(r.randrange(256) for _ in range(r.randrange(1, 40)))   # trailing bytes ignored
        xs.append(x)
    xs += [b"", b"\x00", b"\xff" * 3]
    return xs
def code_inputs(fn, r, n, big):
    xs = [b"", b"\x00", b"\x01", b"\x0f", b"\x10", b"\xff", bytes(range(256)),
          bytes([8] * 144 + [9] * 112 + [7] * 24 + [8] * 8),                       # fixed Huffman literal lengths
          bytes([5] * 30), bytes([1, 1]), bytes([1, 2, 3, 3]), bytes([15] * 7), bytes([1] * 70),
          bytes([1] * 200), bytes(15 * [15]) + bytes([16] * 3)]
    sizes = [2, 3, 15, 16, 17, 31, 100, 257, 1000, 3000]
    while len(xs) < n:
        L = r.choice(sizes) if r.random() < .8 else r.randrange(300); k = r.randrange(7)
        if k == 0: x = [r.randrange(16) for _ in range(L)]
        elif k == 1: x = [r.randrange(256) for _ in range(L)]
        elif k == 2: v = r.randrange(256); x = [v] * L
        elif k == 3: x = [r.choice([0, 0, 0, r.randrange(1, 16)]) for _ in range(L)]
        elif k == 4: x = [min(15, max(1, int(r.gauss(8, 3)))) for _ in range(L)]
        elif k == 5: x = [r.choice([1, 2, 15, 16, 0, 255]) for _ in range(L)]
        else: x = [r.randrange(1, 4) for _ in range(L)]
        xs.append(bytes(x))
    if big:    # counts above 2^17: nextCodes wraps mod 2^32 (140000 ones: code at bits 15 = 140000 * 2^15 > 2^32)
        xs += [b"\x01" * 140000, b"\x01" * 131072, b"\x01" * 131071, bytes(r.randrange(1, 3) for _ in range(70000)),
               bytes(r.randrange(16) for _ in range(100000))]
    return xs

# ---------- machine
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
TAIL = '.section .tohost,"aw"\n.globl tohost\n.globl fromhost\n.align 6\ntohost: .dword 0\nfromhost: .dword 0\n'
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
%s""" + TAIL

def header(fn):
    lines = [l for l in open(os.path.join(WD, fn + ".words")) if l.strip()]
    h = lines[0].split(); words = [int(l, 16) for l in lines[1:]]
    if h[0] == "wa":
        A, N, B, Lf = map(int, h[1:]); wk = lambda n: 8 * (A + B * n) + 8 * (N + 1) + 7
        return words, wk, f"wa A={A} N={N} B={B}: 8(A + B n) + 8(N + 1) + 7"
    S = int(h[0]); return words, (lambda n: 8 * (S + 1) + 7), f"slots={S}: 8(slots + 1) + 7"

def build(fn, words, wk, cases, fill_seed, flip):
    """cases: (input, expected).  layout per case: [in|G][out R|G][pad][G][work WK|G]"""
    r = random.Random(fill_seed); data, tab, off, lay = [], [], 0, []
    for xs, ys in cases:
        R, L, WK = len(ys), len(xs), wk(len(xs))
        i0 = off; o0 = i0 + L + G; w0 = (o0 + R + G + 7) // 8 * 8 + G; off = w0 + WK + G
        lay.append((i0, o0, w0, WK))
        o_fill = r.randbytes(R); w_fill = r.randbytes(WK)
        if flip: o_fill = bytes(255 - b for b in o_fill); w_fill = bytes(255 - b for b in w_fill)
        tab.append(f"  .quad base+{i0}, {L}, base+{w0}, base+{o0}, base+{w0 + WK}, {MAGIC}, 0, 0, 0")
        data.append(bytes(xs) + b"\xAA" * G + o_fill + b"\xAA" * G + b"\x00" * (w0 - G - (o0 + R + G)) + b"\xAA" * G
                    + w_fill + b"\xAA" * G)
    open(p("m.bin"), "wb").write(b"".join(data))
    func = "".join(f"  .word 0x{w:08x}\n" for w in words)
    open(p("m.S"), "w").write(DRIVER % (len(cases), E, func) + f'.data\n.align 4\nbase:\n.incbin "{p("m.bin")}"\n.align 3\ntab:\n'
                              + "\n".join(tab) + "\n")
    open(p("m.ld"), "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{p('m.ld')} -Wl,--no-relax "
       f"-Wl,--build-id=none {p('m.S')} -o {p('m.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('m.elf')}", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    return lay, sym("halt"), sym("base"), sym("tab"), sym("tohost"), off

def qemu(halt, a, n):
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('m.elf')} -display none -serial none -monitor stdio",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version")
    while "pc       %016x" % halt not in hmp("info registers"): pass
    hmp(f'pmemsave {a:#x} {n} "{p("m.q.bin")}"'); q.stdin.write("quit\n"); q.wait()
    return open(p("m.q.bin"), "rb").read()

def common_checks(nm, fn, mem, init, lay, cases, base, tab, size):
    for c, ((i0, o0, w0, WK), (xs, ys)) in enumerate(zip(lay, cases)):
        L, R = len(xs), len(ys)
        tag = (nm, fn, "case", c, xs[:40].hex(), L)
        assert bytes(mem[i0:i0 + L + G]) == bytes(xs) + b"\xAA" * G, ("input/guard", *tag)
        assert bytes(mem[o0:o0 + R]) == ys, ("output", bytes(mem[o0:o0 + R]).hex(), "want", ys.hex(), *tag)
        assert bytes(mem[o0 + R:o0 + R + G]) == b"\xAA" * G, ("output guard", *tag)
        assert bytes(mem[w0 - G:w0]) == b"\xAA" * G, ("work guard below", *tag)
        assert bytes(mem[w0 + WK:w0 + WK + G]) == b"\xAA" * G, ("work guard above", *tag)
        e = tab - base + E * c
        gp, spo, a1 = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56, 64))
        assert gp == MAGIC and spo == base + w0 + WK, ("gp/sp", hex(gp), spo - base - w0 - WK, *tag)
        if fn in LISTS: assert a1 == R, ("a1", a1, R, *tag)

def run(fn, seed, N, mode):
    r = random.Random(seed); words, wk, wkdesc = header(fn)
    xs = scal_inputs(fn, r, N) if "kraft" not in fn and "nextcodes" not in fn else code_inputs(fn, r, N, mode == "qemu" and os.environ.get("BIGN"))
    xs = list(dict.fromkeys(xs))
    open(p("in.txt"), "w").write("".join(f"{fn} {x.hex() or '-'}\n" for x in xs))
    lean = subprocess.check_output(f"{LEAN} --run {os.path.join(D, 'ref.lean')} < {p('in.txt')} 2>/dev/null", shell=True, text=True).split("\n")
    cases = []
    for x, l in zip(xs, lean):
        y = bytes.fromhex(l); assert y == PY[fn](x), ("Lean != Python", fn, x.hex()[:80], y.hex(), PY[fn](x).hex())
        cases.append((x, y))
    assert len(lean) == len(xs) + 1, (len(lean), len(xs))
    msg = f"{fn}: {len(cases)} cases (Lean == Python), work {wkdesc}"
    if mode == "qemu":
        runs = []
        for flip in (0, 1):
            lay, halt, base, tab, tohost, size = build(fn, words, wk, cases, seed, flip)
            init = bytearray(open(p("m.bin"), "rb").read())
            mem = qemu(halt, base, tab + E * len(cases) - base)
            allowed = bytearray(len(mem))                       # 1 = may change
            for i in range(tab - base, len(mem)): allowed[i] = 1
            for (i0, o0, w0, WK), (xs_, ys) in zip(lay, cases):
                for i in range(o0, o0 + len(ys)): allowed[i] = 1
                for i in range(w0, w0 + WK): allowed[i] = 1
            for i in range(len(init)):                          # whole image outside output + work + slots unchanged
                assert allowed[i] or mem[i] == init[i], ("memory outside output + work changed", fn, base + i)
            common_checks("qemu", fn, mem, init, lay, cases, base, tab, size)
            runs.append((mem, lay))
        # work usage and heap/stack separation from the two fills
        used = 0; frac = 0.0; worst = (10**9, None)
        for c, (xs_, ys) in enumerate(cases):
            i0, o0, w0, WK = runs[0][1][c]
            a, b = runs[0][0][w0:w0 + WK], runs[1][0][w0:w0 + WK]
            wr = [x == y for x, y in zip(a, b)]                 # equal in both runs = written
            run_, best = 0, 0
            for v in wr: run_ = 0 if v else run_ + 1; best = max(best, run_)
            assert best > 0, ("work block fully written: heap and stack may have met", fn, c, xs_[:40].hex())
            frac = max(frac, sum(wr) / WK); worst = min(worst, (best, c))
            assert runs[0][0][o0:o0 + len(ys)] == runs[1][0][o0:o0 + len(ys)]
        msg += f"; QEMU x2 fills ok; max fraction of work block written {frac:.3f}, smallest never-written run {worst[0]} bytes"
    else:
        lay, halt, base, tab, tohost, size = build(fn, words, wk, cases, seed, 0)
        init = bytearray(open(p("m.bin"), "rb").read())
        subprocess.run(f"set -o pipefail; {SAIL} --inst-limit 2000000000 --trace-mem --trace-output /dev/stdout {p('m.elf')} 2>&1 "
                       f"| grep -E 'mem\\[W|SUCCESS|FAIL|limit' > {p('sail.log')}", shell=True, check=True, executable="/bin/bash")
        out = open(p("sail.log")).read(); assert "SUCCESS" in out, out[-300:]
        allowed = set(range(tab, tab + E * len(cases)))
        for (i0, o0, w0, WK), (xs_, ys) in zip(lay, cases):
            allowed |= set(range(base + o0, base + o0 + len(ys))) | set(range(base + w0, base + w0 + WK))
        mem = bytearray(init) + bytearray(tab + E * len(cases) - base - len(init)); nw = 0
        for l in out.split("\n"):
            m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
            if not m: continue
            a, v = int(m.group(1), 16), m.group(2); nb = len(v) // 2; nw += 1
            if a < base: assert tohost <= a < tohost + 16, ("Sail write outside data", l); continue
            for j in range(nb):
                assert a + j in allowed, f"unexpected Sail write {l.strip()}"
                mem[a + j - base] = int(v[2 * (nb - 1 - j):2 * (nb - j)], 16)
        common_checks("sail", fn, mem, init, lay, cases, base, tab, size)
        os.system(f"rm -rf {p('sail.log')} {p('m.bin')} {p('m.q.bin')}")      # traces and images can fill the disk
        msg += f"; Sail ok ({nw} writes, all in output + work + slots)"
    print(msg)

if __name__ == "__main__":
    fn, seed, N, mode = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    run(fn, seed, N, mode)
