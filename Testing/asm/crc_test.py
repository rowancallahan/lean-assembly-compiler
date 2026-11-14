#!/usr/bin/env python3
"""Tests of the proved CRC-32 (`Riscv/Examples/Crc.lean`, `crcCode`, words from `Testing/asm/emit_crc.lean` in
`Testing/asm/arr-words/crc.words`) on QEMU and on the Sail C emulator, in the `Implements1` calling convention
(`Spec/Implements1.lean`): a0 = input, a1 = length, a2 = work base (8-aligned), a3 = output, sp = work end.

check N: the known vectors ("" -> 0, "123456789" -> 0xCBF43926, "a", "abc", "The quick brown fox ...") and
N - 5 random inputs (lengths up to 3000).  Each case gets its own input / output (4 bytes) / work block
(2063 bytes = `space n`, at an 8-aligned base), each followed by 16 guard bytes; the driver sets gp to a magic
value before the call and stores gp, sp after it.  Checked on QEMU and Sail: output = zlib.crc32(input)
(little-endian), input, guards and work-block tail unchanged where required, gp and sp restored, and (Sail) every
data write lands in the 4 result bytes or in the work block.
usage: crc_test.py check N"""
import os, random, re, subprocess, sys, zlib
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "ctest"); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
words = [int(l, 16) for l in open(os.path.join(D, "arr-words", "crc.words")) if l.strip()]
G, WK, E = 16, 2063, 72
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
    """per case: [in | G][out 4 | G][pad to 8][work WK | G]"""
    data, tab, off, lay = [], [], 0, []
    for xs in cases:
        L = len(xs); i0 = off; o0 = i0 + L + G; w0 = (o0 + 4 + G + 7) // 8 * 8; off = w0 + WK + G
        lay.append((i0, o0, w0))
        tab.append(f"  .quad base+{i0}, {L}, base+{w0}, base+{o0}, base+{w0 + WK}, {MAGIC}, 0, 0, 0")
        data.append(bytes(xs) + b"\xAA" * G + b"\x55" * 4 + b"\xAA" * G + b"\x00" * (w0 - (o0 + 4 + G))
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
    rng = random.Random(5)
    fixed = [b"", b"123456789", b"a", b"abc", b"The quick brown fox jumps over the lazy dog"]
    cases = [list(x) for x in fixed] + [[rng.randrange(256) for _ in range(rng.choice([rng.randrange(40),
             rng.randrange(3000)]))] for _ in range(max(0, N - len(fixed)))]
    func = "".join(f"  .word 0x{w:08x}\n" for w in words)
    lay, halt, base, tab, size = build(cases, func)
    qmem = qemu(halt, base, tab + E * len(cases) - base)
    r = subprocess.run(f"{SAIL} --inst-limit 2000000000 --trace-mem --trace-output {p('sail.log')} {p('crc.elf')}",
                       shell=True, capture_output=True, text=True)
    assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
    init = bytearray(open(p("crc.bin"), "rb").read()) + bytearray(qmem[size:])
    allowed = set(range(tab, tab + E * len(cases)))
    for (i0, o0, w0) in lay:
        allowed |= set(range(base + o0, base + o0 + 4)) | set(range(base + w0, base + w0 + WK))
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
    for nm, mem in (("qemu", qmem), ("sail", smem)):
        for c, ((i0, o0, w0), xs) in enumerate(zip(lay, cases)):
            L = len(xs)
            assert list(mem[i0:i0 + L + G]) == xs + [0xAA] * G, (nm, "input", L)
            want = zlib.crc32(bytes(xs)).to_bytes(4, "little")
            assert bytes(mem[o0:o0 + 4]) == want, (nm, "crc", L, bytes(mem[o0:o0 + 4]).hex(), want.hex())
            assert list(mem[o0 + 4:o0 + 4 + G]) == [0xAA] * G, (nm, "output guard", L)
            assert list(mem[w0 + WK:w0 + WK + G]) == [0xAA] * G, (nm, "work guard", L)
            e = tab - base + E * c
            gp, spo = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56))
            assert gp == MAGIC and spo == base + w0 + WK, (nm, "gp/sp", hex(gp), spo)
    print(f"crc32: {len(cases)} cases ok (QEMU == Sail == zlib.crc32, incl. '123456789' -> 0xcbf43926; "
          f"lengths up to {max(map(len, cases))})")

if sys.argv[1] == "check": check(int(sys.argv[2]))
