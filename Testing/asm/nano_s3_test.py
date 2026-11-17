#!/usr/bin/env python3
"""Tests of nano's S3 back end (`Nano/S3*.lean`, Testing/notes/NANO_S3.md).
1. sources: nanolib CORPUS + INT_CORPUS + the adversarial edge sources of chain_test.py + random UInt64/Int64 programs,
   with inputs (edge values and random); listed in Testing/asm/ir-words/nano_s3_list.txt;
2. `Testing/asm/emit_nano_s3.lean`: every source through `nanoElabT` (rejected ones skipped), plus random `Ex` trees;
   per case every link of the chain checked on the Lean side (L1, L2, L3, L4, IR interpreter == `nanoRun`), words and
   cases written (`ir-words/nano_s3_<i>`);
3. QEMU, ALL programs in one machine image: per case in the `StartCorrect` convention (a0 input, a1 length, a2 work,
   a3 output, sp work end) at work = memoryNeeded (output == Lean, a0 != flag, sp/gp restored) and memoryNeeded - 1
   (a0 = flag), and the whole data area outside output + work unchanged;
4. Sail smoke: Testing/asm/ir_test.py check 2 on the first SAIL programs (QEMU == Sail == Lean, writes traced).
usage: nano_s3_test.py [R random sources per type] [SAIL programs] [seed]   (from the repo root)"""
import os, random, re, shutil, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Testing", "nano"))
from nanolib import *
R = int(sys.argv[1]) if len(sys.argv) > 1 else 10
NSAIL = int(sys.argv[2]) if len(sys.argv) > 2 else 4
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 7)
IW = os.path.join(D, "ir-words"); os.makedirs(IW, exist_ok=True)
W = os.path.join(D, "ctest", "nano-s3"); shutil.rmtree(W, ignore_errors=True); os.makedirs(W)
sh = lambda c: subprocess.run(c, shell=True, check=True, cwd=ROOT)
EDGE_SRC = [  # copied from Testing/nano/chain_test.py (adversarial; accepted or rejected by nanoElabT)
    "def f (x : Int64) : Int64 := -5", "def f (x : Int64) : Int64 := (-5)",
    "def g (x : Int64) : Int64 := x\ndef f (x : Int64) : Int64 := g -5", "def f (x : Int64) : Int64 := - -5",
    "def f (x y : Int64) : Int64 := x - -y", "def f (x : Int64) : Int64 := 9223372036854775808 + x",
    "def f (x : Int64) : Int64 := 18446744073709551621 * x", "def f (x : Int64) : Int64 := 0 - -9223372036854775808",
    "def f (x : Int64) : Int64 := -9223372036854775808 * -1", "def f (x : Int64) : UInt64 := x",
    "def f (x : UInt64) (y : Int64) : Int64 := y", "def f (x : UInt64) : UInt64 := x * -1",
    "def f (x : UInt64) : UInt64 := g 0x10", "def id (x : UInt64) : UInt64 := x", "def f (x : UInt64) : UInt64 :=\tx",
    "def g (a b : Int64) : Int64 := a - b\ndef f (x y : Int64) : Int64 := g (x)y",
    "def k : Int64 := -1\ndef f (x : Int64) : Int64 := k -1", "def f (x : Int64) : Int64 := x --5",
]
# boundary sources: many parameters, deep nesting, shadowing, a call graph that duplicates bodies when inlined
BOUND_SRC = [
    "def f (a b c d e f g h i j : UInt64) : UInt64 := a + b * c - d + e * f - g + h * i - j",
    "def f (x : UInt64) : UInt64 := let x := x + 1; let x := x * x; let x := x - 3; x",
    "def g (a b c d e f g h : UInt64) : UInt64 := a * h + b * g + c * f + d * e\n"
    "def f (x y : UInt64) : UInt64 := g x y x y x y x y + g y x y x y x y x",
    "def d (x : UInt64) : UInt64 := x + x\ndef d2 (x : UInt64) : UInt64 := d (d x)\ndef d4 (x : UInt64) : UInt64 := d2 (d2 x)\n"
    "def d8 (x : UInt64) : UInt64 := d4 (d4 x)\ndef f (x : UInt64) : UInt64 := d8 (d8 x)",
    "def f : UInt64 := 18446744073709551615 * 18446744073709551615",
    "def f (x : UInt64) : UInt64 := ((((((((x + 1) * 2) - 3) * 4) + 5) * 6) - 7) * 8)",
]
gu, gi = GI(rng, "UInt64"), GI(rng, "Int64")
srcs = list(CORPUS) + list(INT_CORPUS) + EDGE_SRC + BOUND_SRC + [gu.program() for _ in range(R)] + [gi.program() for _ in range(R)]
lst = []
for i, s in enumerate(srcs):
    k = entry_arity(s) if re.search(r"^def", s, re.M) else 0
    st = bool(re.search(r"\bInt64\b", s)) and not re.search(r"\bUInt64\b", s)
    ins = inputs_i(rng, k, 8) if st else inputs(rng, k, 8)
    open(f"{W}/s{i:03}.nano", "wb").write(s.encode())
    lst.append(f"{W}/s{i:03}.nano " + " ".join(",".join(str(x % M) for x in a) if a else "-" for a in ins))
open(os.path.join(IW, "nano_s3_list.txt"), "w").write("\n".join(lst) + "\n")
print(f"{len(srcs)} sources written")
sh("lake env lean Testing/asm/emit_nano_s3.lean")
names = [l.strip() for l in open(os.path.join(IW, "nano_s3_names.txt")) if l.strip()]

# ---- QEMU, all programs in one image
unhex = lambda h: [] if h == "-" else list(bytes.fromhex(h))
G, E, MAGIC = 16, 88, 0x0123456789ABCDEF
progs = []
for nm in names:
    words = [int(l, 16) for l in open(os.path.join(IW, nm + ".words")).read().split("\n")[1:] if l.strip()]
    cases = [tuple(map(unhex, l.split()[:2])) + (int(l.split()[2]),) for l in open(os.path.join(IW, nm + ".cases")) if l.strip()]
    progs.append((nm, words, cases))
runs = [(pi, x, y, WK, True) for pi, (_, _, cs) in enumerate(progs) for x, y, WK in cs] + \
       [(pi, x, y, WK - 1, False) for pi, (_, _, cs) in enumerate(progs) for x, y, WK in cs]
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80800000; .tohost : { *(.tohost) }\n . = 0x80900000; .data : { *(.data) } }\n"
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
  ld t0, 80(s0)
  jalr ra, 0(t0)
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
"""
data, tab, off, lay = [], [], 0, []
for (pi, xs, ys, WK, fits) in runs:
    L, Rn = len(xs), len(ys)
    i0 = off; o0 = i0 + L + G; w0 = (o0 + Rn + G + 7) // 8 * 8; off = w0 + WK + G
    lay.append((i0, o0, w0))
    tab.append(f"  .quad base+{i0}, {L}, base+{w0}, base+{o0}, base+{w0 + WK}, {MAGIC}, 0, 0, 0, 0, f{pi}")
    data.append(bytes(xs) + b"\xAA" * G + b"\x55" * Rn + b"\xAA" * G + b"\x00" * (w0 - (o0 + Rn + G)) + b"\x77" * WK + b"\xAA" * G)
init = b"".join(data)
open(f"{W}/d.bin", "wb").write(init)
funcs = "".join(f".align 3\nf{pi}:\n" + "".join(f"  .word 0x{w:08x}\n" for w in ws) for pi, (_, ws, _) in enumerate(progs))
src = DRIVER % (len(runs), E) + funcs + '.section .tohost,"aw"\n.globl tohost\n.globl fromhost\n.align 6\ntohost: .dword 0\nfromhost: .dword 0\n' + \
    f'.data\n.align 4\nbase:\n.incbin "{W}/d.bin"\n.align 3\ntab:\n' + "\n".join(tab) + "\n"
open(f"{W}/t.S", "w").write(src); open(f"{W}/m.ld", "w").write(LD)
sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{W}/m.ld -Wl,--no-relax "
   f"-Wl,--build-id=none {W}/t.S -o {W}/t.elf")
syms = subprocess.check_output(f"riscv64-linux-gnu-nm {W}/t.elf", shell=True, text=True)
sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
halt, base, tabA = sym("halt"), sym("base"), sym("tab")
q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {W}/t.elf -display none -serial none -monitor stdio",
                     shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
def hmp(c):
    q.stdin.write(c + "\n"); buf = ""
    while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
    return buf
hmp("info version")
while "pc       %016x" % halt not in hmp("info registers"): pass
hmp(f'pmemsave {base:#x} {tabA + E * len(runs) - base} "{W}/q.bin"'); q.stdin.write("quit\n"); q.wait()
mem = open(f"{W}/q.bin", "rb").read()
for c, ((i0, o0, w0), (pi, xs, ys, WK, fits)) in enumerate(zip(lay, runs)):
    nm = progs[pi][0]; Rn = len(ys)
    # outside the output and work blocks nothing changed
    assert mem[i0:o0] == init[i0:o0], (nm, "input / guard")
    assert mem[o0 + Rn:w0] == init[o0 + Rn:w0], (nm, "output guard")
    assert mem[w0 + WK:w0 + WK + G] == init[w0 + WK:w0 + WK + G], (nm, "work guard")
    e = tabA - base + E * c
    gp, spo, a1, a0 = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56, 64, 72))
    assert spo == base + w0 + WK, (nm, "sp", hex(spo))
    if fits:
        assert list(mem[o0:o0 + Rn]) == ys, (nm, "output", bytes(mem[o0:o0 + Rn]).hex(), bytes(ys).hex())
        assert a0 != 2 ** 64 - 1, (nm, "flag at memoryNeeded")
        assert gp == MAGIC, (nm, "gp")
    else:
        assert a0 == 2 ** 64 - 1, (nm, "no flag at memoryNeeded - 1", hex(a0))
n = sum(len(cs) for _, _, cs in progs)
print(f"QEMU: {len(progs)} programs, {n} cases x 2 ok (output == Lean at memoryNeeded, flag at memoryNeeded - 1, "
      f"nothing outside output + work changed); code {min(len(w) for _, w, _ in progs)}..{max(len(w) for _, w, _ in progs)} words")
# ---- Sail smoke (QEMU == Sail == Lean, Sail writes traced): the first cases of a few programs
for nm in names[:NSAIL]: sh(f"python3 Testing/asm/ir_test.py check 2 {nm}")
shutil.rmtree(os.path.join(D, "ctest"), ignore_errors=True)
print(f"Sail smoke: {NSAIL} programs x 2 cases x 2 ok")
