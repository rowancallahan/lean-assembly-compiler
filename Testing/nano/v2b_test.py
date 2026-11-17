#!/usr/bin/env python3
"""nano v2 small backend on QEMU + the Sail C emulator (words/cases from Testing/asm/emit_nano_v2b.lean).
Convention: a0 = input, a1 = length, a2 = work base (8-aligned), a3 = output, sp = work end.
Per case (input, status, expected bytes), twice:
* work WK = 4096 bytes: status 0 ⇒ output bytes = Lean's, a1 = length, a0 = 0; status s ≠ 0 ⇒ a0 = s, a1 = 0;
* work 8 bytes (too small): a0 = 2^64 - 1 (out of memory).
Always: sp, gp unchanged, input and guards unchanged, (Sail) every data write inside output + work.
usage: v2b_test.py name"""
import os, re, subprocess, sys
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "asm")
FN = sys.argv[1]
W = os.path.join(D, "ctest", "nv2-" + FN); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
unhex = lambda h: [] if h == "-" else list(bytes.fromhex(h))
CASES = [(unhex(a), int(s), unhex(y)) for a, s, y in (l.split() for l in open(os.path.join(D, "ir-words", FN + ".cases")) if l.strip())]
words = [int(l, 16) for l in open(os.path.join(D, "ir-words", FN + ".words")).read().split()[2:]]
G, E, BIG, SMALL = 16, 80, 4096, 8
MAGIC = 0x0123456789ABCDEF
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
  sd a0, 72(s0)
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
runs = [(x, s, y, BIG) for x, s, y in CASES] + [(x, s, y, SMALL) for x, s, y in CASES]
data, tab, off, lay = [], [], 0, []
for x, s, y, WK in runs:
    R = len(y); L = len(x)
    i0 = off; o0 = i0 + L + G; w0 = (o0 + R + G + 7) // 8 * 8; off = w0 + WK + G
    lay.append((i0, o0, w0))
    tab.append(f"  .quad base+{i0}, {L}, base+{w0}, base+{o0}, base+{w0 + WK}, {MAGIC}, 0, 0, 0, 0")
    data.append(bytes(x) + b"\xAA" * G + b"\x55" * R + b"\xAA" * G + b"\x00" * (w0 - (o0 + R + G)) + b"\x77" * WK + b"\xAA" * G)
open(p("t.bin"), "wb").write(b"".join(data))
func = "".join(f"  .word 0x{w:08x}\n" for w in words)
src = DRIVER % (len(runs), E, func) + f'.data\n.align 4\nbase:\n.incbin "{p("t.bin")}"\n.align 3\ntab:\n' + "\n".join(tab) + "\n"
open(p("t.S"), "w").write(src); open(p("m.ld"), "w").write(LD)
sh(f"riscv64-linux-gnu-gcc -march=rv64im_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{p('m.ld')} -Wl,--no-relax "
   f"-Wl,--build-id=none {p('t.S')} -o {p('t.elf')}")
syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('t.elf')}", shell=True, text=True)
sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
halt, base, tabA, size = sym("halt"), sym("base"), sym("tab"), off
q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('t.elf')} -display none -serial none -monitor stdio",
                     shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
def hmp(c):
    q.stdin.write(c + "\n"); buf = ""
    while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
    return buf
hmp("info version")
while "pc       %016x" % halt not in hmp("info registers"): pass
n = tabA + E * len(runs) - base
hmp(f'pmemsave {base:#x} {n} "{p("q.bin")}"'); q.stdin.write("quit\n"); q.wait()
qmem = open(p("q.bin"), "rb").read()
subprocess.run(f"set -o pipefail; {SAIL} --inst-limit 400000000 --trace-mem --trace-output /dev/stdout {p('t.elf')}"
               f" 2>&1 | grep -E 'mem\\[W|SUCCESS|FAIL|limit' > {p('sail.log')}", shell=True, executable="/bin/bash")
out = open(p("sail.log")).read()
assert "SUCCESS" in out, out[-500:]
init = bytearray(open(p("t.bin"), "rb").read()) + bytearray(qmem[size:])
allowed = set(range(tabA, tabA + E * len(runs)))
for (i0, o0, w0), (x, s, y, WK) in zip(lay, runs):
    allowed |= set(range(base + o0, base + o0 + len(y))) | set(range(base + w0, base + w0 + WK))
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
    for c, ((i0, o0, w0), (x, s, y, WK)) in enumerate(zip(lay, runs)):
        L, R = len(x), len(y)
        assert list(mem[i0:i0 + L + G]) == x + [0xAA] * G, (nm, "input", L)
        assert list(mem[o0 + R:o0 + R + G]) == [0xAA] * G, (nm, "output guard", L)
        assert list(mem[w0 + WK:w0 + WK + G]) == [0xAA] * G, (nm, "work guard", L)
        e = tabA - base + E * c
        gp, spo, a1, a0 = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56, 64, 72))
        assert spo == base + w0 + WK and gp == MAGIC, (nm, "sp/gp")
        if WK == SMALL:
            assert a0 == 2 ** 64 - 1, (nm, FN, "oom flag", hex(a0))
        elif s == 0:
            assert bytes(mem[o0:o0 + R]) == bytes(y) and a1 == R and a0 == 0, (nm, FN, L, bytes(mem[o0:o0 + R]).hex(), a0, a1)
        else:
            assert a0 == s and a1 == 0, (nm, FN, "status", a0, a1, s)
st = sorted(set(s for _, s, _ in CASES))
print(f"{FN}: {len(CASES)} cases x 2 ok (QEMU == Sail == Lean `Prog.eval`; statuses {st}; OOM flag with {SMALL}-byte work; "
      f"writes only in output + work; {len(words)} words)")
