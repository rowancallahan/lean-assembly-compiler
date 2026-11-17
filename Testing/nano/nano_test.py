#!/usr/bin/env python3
"""(6) nanoGen output vs `Prog.eval` on QEMU (qemu-riscv64 user mode) and on the Sail C simulator.
usage: nano_test.py [N_random_programs] [seed]
Programs = CORPUS + N random ones; per program 6 input vectors.  Lean (`Nano.Gen`) elaborates, compiles and evaluates."""
import os, random, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nanolib import *
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "work"); os.makedirs(W, exist_ok=True)
ROOT = os.path.abspath(os.path.join(D, "..", ".."))
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
N = int(sys.argv[1]) if len(sys.argv) > 1 else 20
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
INT = os.environ.get("NANO_INT") == "1"  # Int64 programs (INT_CORPUS + GI), signed inputs as their two's complement bits
base = INT_CORPUS if INT else CORPUS
progs = list(base); g = GI(rng, "Int64") if INT else G(rng)
while len(progs) < len(base) + N: progs.append(g.program())
cases = [(s, [[a % M for a in v] for v in inputs_i(rng, entry_arity(s))] if INT else inputs(rng, entry_arity(s))) for s in progs]
lit = lambda s: '"' + s.replace("\\", "\\\\").replace("\n", "\\n") + '"'
lean = ["import Nano.Gen", "open Nano", "def hex (xs : List UInt8) : String := String.join (xs.map fun b => (if b < 16 then \"0\" else \"\") ++ String.ofList (Nat.toDigits 16 b.toNat))",
        "def run (src : String) (ins : List (List UInt64)) : IO Unit := do",
        "  match nanoCompile src.toUTF8.toList with",
        "  | none => IO.println \"REJECT\"",
        "  | some c => for a in ins do IO.println s!\"{hex c} {a} {(nanoElab src.toUTF8.toList).bind (·.eval a)}\"",
        "def main : IO Unit := do"]
for s, ins in cases: lean.append(f"  IO.println \"PROG\"; run {lit(s)} {ins}".replace("], [", "], ["))
open(f"{W}/emit.lean", "w").write("\n".join(lean) + "\n")
out = subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH lake env lean --run {W}/emit.lean", shell=True, check=True, capture_output=True, text=True).stdout
rows = []  # (prog index, code bytes, args, expected)
pi = -1
for l in out.splitlines():
    if l == "PROG": pi += 1; continue
    if "warning" in l or l.startswith(" ") or not l: continue
    assert l != "REJECT", ("rejected", progs[pi])
    m = re.fullmatch(r"([0-9a-f]+) \[([\d, ]*)\] \(some (\d+)\)", l); assert m, l
    rows.append((pi, bytes.fromhex(m.group(1)), [int(x) for x in m.group(2).split(",") if x.strip()], int(m.group(3))))
assert pi == len(progs) - 1
subprocess.run(f"riscv64-linux-gnu-gcc -O1 -static -march=rv64g -mabi=lp64d {D}/driver.c -o {W}/driver", shell=True, check=True)
nq = 0
for pi, code, args, want in rows:
    open(f"{W}/code.bin", "wb").write(code); open(f"{W}/args.bin", "wb").write(b"".join(a.to_bytes(8, "little") for a in args))
    got = int.from_bytes(subprocess.run(f"qemu-riscv64 {W}/driver {W}/code.bin {W}/args.bin", shell=True, check=True, capture_output=True).stdout, "little")
    assert got == want, ("QEMU", progs[pi], args, got, want); nq += 1
print(f"QEMU: {nq} (program, input) pairs of {len(progs)} programs == Prog.eval")
# Sail: one bare-metal ELF; per case: code | args | out word | stack (4 KiB), driver calls the code and stores sp
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
data = b""; tab = []; ST = 8192
for pi, code, args, want in rows:
    o = len(data); code = code + b"\0" * (-len(code) % 8)
    a0 = o + len(code) + 1; out = a0 + 8 * len(args) + 3 + (-(a0 + 8 * len(args) + 3) % 8) + 1; wk = out + 8 + 7 + (-(out + 8 + 7) % 8)
    tab.append(f"  .quad base+{o}, base+{a0}, {8 * len(args)}, base+{wk}, base+{out}, base+{wk + ST}, 0, 0")
    data += code + b"\x77" + b"".join(a.to_bytes(8, "little") for a in args) + b"\x77" * (out - a0 - 8 * len(args)) + b"\x55" * 8 + b"\x77" * (wk - out - 8) + b"\0" * ST
open(f"{W}/s.bin", "wb").write(data)
S = f""".section .text.start
.globl _start
_start: lla s0, tab
  li s2, {len(rows)}
1: ld t3, 0(s0)
  ld a0, 8(s0)
  ld a1, 16(s0)
  ld a2, 24(s0)
  ld a3, 32(s0)
  ld sp, 40(s0)
  jalr ra, t3, 0
  sd sp, 48(s0)
  sd a0, 56(s0)
  addi s0, s0, 64
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
.section .tohost,"aw"
.globl tohost
.align 6
tohost: .dword 0
.data
.align 4
base:
.incbin "{W}/s.bin"
.align 3
tab:
""" + "\n".join(tab) + "\n"
open(f"{W}/s.S", "w").write(S); open(f"{W}/m.ld", "w").write(LD)
subprocess.run(f"riscv64-linux-gnu-gcc -march=rv64im_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{W}/m.ld -Wl,--no-relax -Wl,--build-id=none {W}/s.S -o {W}/s.elf", shell=True, check=True)
syms = subprocess.check_output(f"riscv64-linux-gnu-nm {W}/s.elf", shell=True, text=True)
sym = lambda x: int(re.search(rf"(\w+) \w {x}\n", syms).group(1), 16)
base, tabA = sym("base"), sym("tab")
r = subprocess.run(f"set -o pipefail; {SAIL} --inst-limit 2000000000 --trace-mem --trace-output /dev/stdout {W}/s.elf 2>&1 | grep -E 'mem\\[W|SUCCESS|FAIL|limit' > {W}/sail.log", shell=True, executable="/bin/bash")
log = open(f"{W}/sail.log").read(); assert "SUCCESS" in log, log[-300:]
mem = {}
for l in log.splitlines():
    m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
    if m:
        a, v = int(m.group(1), 16), m.group(2)
        for j in range(len(v) // 2): mem[a + j] = int(v[2 * (len(v) // 2 - 1 - j):2 * (len(v) // 2 - j)], 16)
off = 0
for c, (pi, code, args, want) in enumerate(rows):
    o = off; cl = len(code) + (-len(code) % 8)
    a0 = o + cl + 1; out = a0 + 8 * len(args) + 3 + (-(a0 + 8 * len(args) + 3) % 8) + 1; wk = out + 8 + 7 + (-(out + 8 + 7) % 8)
    got = int.from_bytes(bytes(mem[base + out + j] for j in range(8)), "little")
    assert got == want, ("Sail", progs[pi], args, got, want)
    sp, st = (int.from_bytes(bytes(mem[tabA + 64 * c + k + j] for j in range(8)), "little") for k in (48, 56))
    assert sp == base + wk + ST, ("Sail sp", sp); assert st == base + a0, ("Sail a0 (status)", st)
    # every write is the output word or the work block
    off = wk + ST
allowed = set()
off = 0
for c, (pi, code, args, want) in enumerate(rows):
    cl = len(code) + (-len(code) % 8); a0 = off + cl + 1; out = a0 + 8 * len(args) + 3 + (-(a0 + 8 * len(args) + 3) % 8) + 1; wk = out + 8 + 7 + (-(out + 8 + 7) % 8)
    allowed |= set(range(base + out, base + out + 8)) | set(range(base + wk, base + wk + ST)); off = wk + ST
allowed |= set(range(tabA, tabA + 64 * len(rows)))
for l in log.splitlines():
    m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
    if m:
        a, n = int(m.group(1), 16), len(m.group(2)) // 2
        if a < base: continue  # tohost
        assert all(a + j in allowed for j in range(n)), ("write outside output/work", l)
print(f"Sail: {len(rows)} (program, input) pairs == Prog.eval; sp restored; a0 != oom flag; every write in the (unaligned) output word / work block")
