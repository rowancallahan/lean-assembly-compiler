#!/usr/bin/env python3
"""fuzz4: QEMU differential test of Frontx entry points (adlere adlerstatee replacexe fromoptione smalle swape addpointse
zeroxe neste nontailsumrec nontaillengthrec fiblen) against executed Lean (`emit.lean`) and independent Python references.
usage: CASESDIR=dir CTEST=dir [HUGE=1|ONLYHUGE=1] [FILL=seed] python3 frontx_fuzz4.py check N fn
Per case: [in|G][out R|G][pad G][work = space n |G]; out pre-filled with random bytes (FILL), work with 0x77, guards 0xAA/0xBB.
Checks: output = Lean = Python ref, gp/sp restored, guards intact, all QEMU memory outside out+work unchanged, and the
stack use (lowest touched work byte) never exceeds the work block."""
import os, random, re, subprocess, sys, zlib
D = os.path.dirname(os.path.abspath(__file__)); W = os.environ.get("CTEST", "/tmp/fuzz4ctest"); os.makedirs(W, exist_ok=True)
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
M8 = 2 ** 64
b = lambda xs, i: xs[i] if i < len(xs) else 0
u16 = lambda xs, i: b(xs, i) | b(xs, i + 1) << 8
le = lambda n, k: (n % 2 ** (8 * k)).to_bytes(k, "little")
def adler(xs, a=1, bb=0):
    for c in xs: a = (a + c) % 65521; bb = (bb + a) % 65521
    return a, bb
def fibi(n):
    x, y = 0, 1
    for _ in range(n): x, y = y, x + y
    return x
REFS = {
  "adlere": lambda x: le(zlib.adler32(bytes(x)), 4),
  "adlerstatee": lambda x: le(adler(x)[0], 8) + le(adler(x)[1], 8),
  "replacexe": lambda x: le(u16(x, 4), 8) + le(u16(x, 2), 8),
  "fromoptione": lambda x: le(b(x, 0) if b(x, 1) == 0 else b(x, 2), 8),
  "smalle": lambda x: bytes([int(b(x, 0) != 1)]),
  "swape": lambda x: le(b(x, 2), 8) + le(b(x, 0) + (b(x, 1) << 8), 8),
  "addpointse": lambda x: le(b(x, 0) + b(x, 2), 8) + le(b(x, 1) + b(x, 3), 8),
  "zeroxe": lambda x: le(0, 8) + le(u16(x, 2), 8),
  "neste": lambda x: le(b(x, 0), 1) + le(b(x, 1) + 1, 4) + le(b(x, 2) // 16, 8),
  "nontailsumrec": lambda x: le(sum(x), 8), "nontaillengthrec": lambda x: le(len(x), 8),
  "fiblen": lambda x: le(fibi(len(x)), 8)}
FN = sys.argv[3]
unhex = lambda h: [] if h == "-" else list(bytes.fromhex(h))
CASES = [] if os.environ.get("ONLYHUGE") else [tuple(map(unhex, l.split())) for l in open(os.path.join(os.environ["CASESDIR"], FN + ".cases")) if l.strip()]
if (os.environ.get("HUGE") or os.environ.get("ONLYHUGE")) and FN != "fiblen":  # up to maxLen = 2^20; Python refs only
    rr = random.Random(7)
    for xs in ([0] * 2 ** 20, [255] * 2 ** 20, [rr.randrange(256) for _ in range(2 ** 20)], [rr.randrange(2) * 255 for _ in range(2 ** 20 - 1)],
               [255] * 65521, [0] * 65520, [rr.randrange(256) for _ in range(65522)], [255] * 5552, [255] * 5553):
        CASES.append((xs, list(REFS[FN](xs))))
lines = [l for l in open(os.path.join(os.environ["CASESDIR"], FN + ".words")) if l.strip()]
words = [int(l, 16) for l in lines[1:]]
G, E = 16, 72
REC = int(lines[0].split()[1]) if lines[0].startswith("rec") else None
wk = lambda L: REC * (L + 1) + 32 if REC else 8 * (int(lines[0]) + 1) + 7   # = space n
MAGIC = 0x0123456789ABCDEF
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
  addi s0, s0, %d
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
func:
%s""" + TAIL

rf = random.Random(int(os.environ.get("FILL", "1")))
def build(cases, func):
    """per case: [in | G][out R | G][pad G][work | G]; random fills; returns layout"""
    data, tab, off, lay = [], [], 0, []
    for xs, ys in cases:
        R = len(ys); L = len(xs); WK = wk(L)
        i0 = off; o0 = i0 + L + G; w0 = (o0 + R + G + G + 7) // 8 * 8; off = w0 + WK + G
        lay.append((i0, o0, w0))
        tab.append(f"  .quad base+{i0}, {L}, base+{w0}, base+{o0}, base+{w0 + WK}, {MAGIC}, 0, 0, 0")
        data.append(bytes(xs) + b"\xAA" * G + rf.randbytes(R) + b"\xAA" * G + b"\xBB" * (w0 - (o0 + R + G))
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
    cases = CASES[:N]
    func = "".join(f"  .word 0x{w:08x}\n" for w in words)
    lay, halt, base, tab, size = build(cases, func)
    init = open(p("crc.bin"), "rb").read()
    qmem = qemu(halt, base, tab + E * len(cases) - base)
    keep = bytearray(qmem[:size])
    for (i0, o0, w0), (xs, ys) in zip(lay, cases):   # outside out+work: must equal the initial image
        keep[o0:o0 + len(ys)] = init[o0:o0 + len(ys)]; keep[w0:w0 + wk(len(xs))] = init[w0:w0 + wk(len(xs))]
    assert bytes(keep) == init, "QEMU: memory changed outside output/work"
    worst = 0
    for c, ((i0, o0, w0), (xs, ys)) in enumerate(zip(lay, cases)):
        L, R, WK = len(xs), len(ys), wk(len(xs)); mem = qmem
        assert list(mem[i0:i0 + L + G]) == xs + [0xAA] * G, ("input", L)
        want = bytes(ys); ref = REFS[FN](xs)
        assert want == ref, ("Lean != Python reference", FN, L, want.hex()[:40], ref.hex()[:40])
        assert bytes(mem[o0:o0 + R]) == want, (FN, L, bytes(mem[o0:o0 + R]).hex(), want.hex())
        e = tab - base + E * c
        gp, spo, a1 = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56, 64))
        assert gp == MAGIC and spo == base + w0 + WK, ("gp/sp", hex(gp), spo)
        wmem = mem[w0:w0 + WK]; low = next((k for k in range(WK) if wmem[k] != 0x77), WK)
        worst = max(worst, (WK - low) / WK)
    print(f"{FN}: {len(cases)} cases ok (QEMU == Lean == Python; input lengths up to {max(len(x) for x, _ in cases)}; {len(words)} words; "
          f"work " + (f"{REC}(n+1)+32" if REC else f"{wk(0)}") + f" bytes; max work touched {worst:.0%})")

check(int(sys.argv[2]))
