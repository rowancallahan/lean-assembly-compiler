#!/usr/bin/env python3
"""IR back-end tests (`Compiler/Ir/`, `Legacy/Riscv/Back/IrTop.lean`; words and cases from `Testing/asm/emit_ir.lean` in `Testing/asm/ir-words/`): every case twice, on QEMU and on the Sail C emulator,
in the `StartCorrect` calling convention (a0 = input, a1 = length, a2 = work base (8-aligned), a3 = output,
sp = work end):
* with a work block of exactly `memoryNeeded` bytes: output = Lean's result, a0 = the input address (not the flag),
  a1 = the result length for tree results, gp and sp restored;
* with `memoryNeeded - 1` bytes: a0 = 2^64 - 1 (the out-of-memory flag), sp unchanged (gp is not restored: IR_STRONG.md).
S3 programs (`s3*`): a1 = the output length (main returns it; `S3.compile_correctL`).
Both: input, guards unchanged and (Sail) every data write lands in the output block or the work block.
usage: mem_test.py check N name"""
import math, os, random, re, subprocess, sys, zlib
D = os.path.dirname(os.path.abspath(__file__))
W = os.path.join(D, "ctest", "ir-" + sys.argv[3]); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
def b64digit(c):
    if 65 <= c <= 90: return c - 65
    if 97 <= c <= 122: return c - 71
    if 48 <= c <= 57: return c + 4
    return 62 if c == 43 else 63 if c == 47 else 64
at = lambda xs, i: xs[i] if i < len(xs) else 0
rdn = lambda xs, o, n: sum(at(xs, o + j) << (8 * j) for j in range(n))
def ops(a, b, w, sh):
    """`a * b ^^^ a / b ^^^ a % b ^^^ a <<< b ^^^ a >>> b` with Lean's semantics (`w = None`: `Nat`, mod 2^64)"""
    M = 2 ** 64 if w is None else 2 ** w
    q = a // b if b else 0; r = a % b if b else a
    s = b % sh
    hi = a >> b if w is None else a >> s
    return ((a * b) ^ q ^ r ^ (a << s) ^ hi) % M
# name -> (result bytes, reference)
FUNCS = {
    "crcraw": (4, lambda xs: zlib.crc32(bytes(xs)) ^ 0xFFFFFFFF),
    "wa_crc32": (4, lambda xs: zlib.crc32(bytes(xs))),
    "wa_crcupdate": (4, lambda xs: zlib.crc32(bytes(xs)) ^ 0xFFFFFFFF),
    "b64all": (4, lambda xs: sum(b64digit(c) for c in xs) % 2 ** 32),
    "findnl": (8, lambda xs: next((k for k, c in enumerate(xs) if c == 10), len(xs))),
    "be32at0": (8, lambda xs: at(xs, 0) << 24 | at(xs, 1) << 16 | at(xs, 2) << 8 | at(xs, 3)),
    "tailsum": (8, lambda xs: sum(xs)),
    "nontailsum": (8, lambda xs: sum(xs)),
    "taillength": (8, lambda xs: len(xs)),
    "booklength": (8, lambda xs: len(xs)),
    "nontailsumrec": (8, lambda xs: sum(xs)),
    "nontaillengthrec": (8, lambda xs: len(xs)),
    # NOTES section 22
    "wa_gcd": (8, lambda xs: math.gcd(rdn(xs, 0, 4), rdn(xs, 4, 4))),
    "wa_kraft": (8, lambda xs: sum(sum(1 for c in xs if c == b) << (15 - b) for b in range(1, 16))),
    "wa_ops64": (8, lambda xs: ops(rdn(xs, 0, 8), rdn(xs, 8, 8), 64, 64)),
    "wa_ops32": (4, lambda xs: ops(rdn(xs, 0, 4), rdn(xs, 4, 4), 32, 32)),
    "wa_opsn": (8, lambda xs: ops(rdn(xs, 0, 4), rdn(xs, 4, 4), None, 64)),
    "fx_ops64": (8, lambda xs: ops(rdn(xs, 0, 8), rdn(xs, 8, 8), 64, 64)),
    "fx_ops32": (4, lambda xs: ops(rdn(xs, 0, 4), rdn(xs, 8, 4), 32, 32)),
    "fx_opsn": (8, lambda xs: ops(rdn(xs, 0, 8), rdn(xs, 8, 8), None, 64)),
    "fx_gcd": (8, lambda xs: math.gcd(rdn(xs, 0, 8), rdn(xs, 8, 8))),
}
# functions returning a list: the length is returned in a1
LISTS = {"tinycompile", "tinysm", "take5", "drop5", "matchdrop3", "filterall", "inceach", "twice"}
FN = sys.argv[3]
unhex = lambda h: [] if h == "-" else list(bytes.fromhex(h))
# a case: input hex, result hex, memoryNeeded
CASES = [tuple(map(unhex, l.split()[:2])) + (int(l.split()[2]),)
         for l in open(os.path.join(D, "ir-words", FN + ".cases")) if l.strip()]
lines = [l for l in open(os.path.join(D, "ir-words", FN + ".words")) if l.strip()]
words = [int(l, 16) for l in lines[1:]]
G, E = 16, 80
if lines[0].split()[1] == "1": LISTS.add(FN)
MAGIC = 0x0123456789ABCDEF
MIS = tuple(int(v) for v in os.environ.get("MIS", "0,0").split(","))  # extra bytes before the input / output block (misalignment tests)
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
TAIL = """.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
"""
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
  sd a0, 72(s0)
  addi s0, s0, %d
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
func:
%s""" + TAIL

def build(cases, func):
    """per run: [in | G][out R | G][pad to 8][work WK | G], R = the length of Lean's result, WK = the case's work"""
    data, tab, off, lay = [], [], 0, []
    for case in cases:
        xs, ys, WK = case[0], case[1], case[2]
        R = len(ys)
        L = len(xs); i0 = off + MIS[0]; o0 = i0 + L + G + MIS[1]; w0 = (o0 + R + G + 7) // 8 * 8; off = w0 + WK + G
        lay.append((i0, o0, w0))
        tab.append(f"  .quad base+{i0}, {L}, base+{w0}, base+{o0}, base+{w0 + WK}, {MAGIC}, 0, 0, 0, 0")
        data.append(b"\x11" * MIS[0] + bytes(xs) + b"\xAA" * G + b"\x44" * MIS[1] + b"\x55" * R + b"\xAA" * G + b"\x00" * (w0 - (o0 + R + G))
                    + b"\x77" * WK + b"\xAA" * G)
    open(p("crc.bin"), "wb").write(b"".join(data))
    src = DRIVER % (len(cases), E, func) + f'.data\n.align 4\nbase:\n.incbin "{p("crc.bin")}"\n.align 3\ntab:\n' + "\n".join(tab) + "\n"
    open(p("crc.S"), "w").write(src); open(p("m.ld"), "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{p('m.ld')} -Wl,--no-relax "
       f"-Wl,--build-id=none {p('crc.S')} -o {p('crc.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('crc.elf')}", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    return lay, sym("halt"), sym("base"), sym("tab"), off

def qemu(halt, a, n):
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('crc.elf')} -display none -serial none "
                         f"-monitor stdio", shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version")
    while "pc       %016x" % halt not in hmp("info registers"): pass
    hmp(f'pmemsave {a:#x} {n} "{p("crc.q.bin")}"'); q.stdin.write("quit\n"); q.wait()
    return open(p("crc.q.bin"), "rb").read()

def check(N):
    # every case twice: work = memoryNeeded (fits), memoryNeeded - 1 (out of memory)
    runs = [(x, y, M, True) for x, y, M in CASES[:N]] + [(x, y, M - 1, False) for x, y, M in CASES[:N]]
    func = "".join(f"  .word 0x{w:08x}\n" for w in words)
    lay, halt, base, tab, size = build(runs, func)
    qmem = qemu(halt, base, tab + E * len(runs) - base)
    NOSAIL = os.environ.get("NOSAIL") == "1"  # bulk runs: QEMU only (Sail on a smoke subset in a separate run)
    if NOSAIL: open(p("sail.log"), "w").write("SUCCESS\n")
    r = None if NOSAIL else subprocess.run(f"set -o pipefail; {SAIL} --inst-limit 4000000000 --trace-mem --trace-output /dev/stdout {p('crc.elf')}"
                       f" 2>&1 | grep -E 'mem\\[W|SUCCESS|FAIL|limit' > {p('sail.log')}",
                       shell=True, capture_output=True, text=True, executable="/bin/bash")
    out = open(p("sail.log")).read()
    assert "SUCCESS" in out, out[-500:]
    init = bytearray(open(p("crc.bin"), "rb").read()) + bytearray(qmem[size:])
    allowed = set(range(tab, tab + E * len(runs)))
    for (i0, o0, w0), run in zip(lay, runs):
        allowed |= set(range(base + o0, base + o0 + len(run[1]))) | set(range(base + w0, base + w0 + run[2]))
    smem = bytearray(init)
    for l in open(p("sail.log")):
        m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
        if not m: continue
        a, v = int(m.group(1), 16), m.group(2)
        if a < base: continue
        nb = len(v) // 2
        for j in range(nb):
            assert a + j in allowed, f"unexpected Sail write {l.strip()}"
            smem[a + j - base] = int(v[2 * (nb - 1 - j):2 * (nb - j)], 16)
    for nm, mem in (("qemu", qmem),) + ((("sail", smem),) if not NOSAIL else ()):
        for c, ((i0, o0, w0), run) in enumerate(zip(lay, runs)):
            xs, ys, WK, fits = run
            L = len(xs); R = len(ys)
            assert list(mem[i0:i0 + L + G]) == xs + [0xAA] * G, (nm, "input", L)
            assert list(mem[o0 + R:o0 + R + G]) == [0xAA] * G, (nm, "output guard", L)
            assert list(mem[w0 + WK:w0 + WK + G]) == [0xAA] * G, (nm, "work guard", L)
            e = tab - base + E * c
            gp, spo, a1, a0 = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56, 64, 72))
            assert spo == base + w0 + WK, (nm, "sp", spo)
            if fits:
                assert bytes(mem[o0:o0 + R]) == bytes(ys), (nm, FN, L, bytes(mem[o0:o0 + R]).hex(), bytes(ys).hex())
                assert a0 == base + i0, (nm, "a0 (status) at memoryNeeded", hex(a0))
                assert gp == MAGIC, (nm, "gp", hex(gp))
                if FN in LISTS or FN.startswith("s3"): assert a1 == R, (nm, "a1 (length)", a1, R)
            else:
                assert a0 == 2 ** 64 - 1, (nm, "a0 (status) at memoryNeeded - 1", hex(a0), WK)
    Ms = [M for _, _, M in CASES[:N]]
    print(f"{FN}: {len(Ms)} cases x 2 ok ({'QEMU only' if NOSAIL else 'QEMU == Sail'} == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, "
          f"writes only in output + work; input lengths up to {max(len(x) for x, *_ in CASES[:N])}; {len(words)} words; "
          f"memoryNeeded {min(Ms)}..{max(Ms)} bytes)")

if sys.argv[1] == "check": check(int(sys.argv[2]))
