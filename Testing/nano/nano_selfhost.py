#!/usr/bin/env python3
"""Self-hosting data point.  The assembler stage `Nano.asm` of the nano compiler runs as RISC-V code produced by OUR
compiler (machine theorem `Nano.Self.nanoAsm.implements1`, words `frontx-words/nanoasm.words`):
 (a) frontx_test: its records->code cases (nanoElab+genR of every program) on QEMU and Sail == executed Lean `asm`;
 (b) pipeline: source -> (Lean) nanoElab + genR -> records -> (the BINARY, QEMU system mode) code; code == Lean `nanoGen`;
     the code is run on qemu-riscv64 for 6 argument vectors and compared with `Prog.eval`.
usage: nano_selfhost.py [N random programs] (seed 3), run from the repo root"""
import os, random, subprocess, sys, shutil
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", "..")); W = os.path.join(D, "work"); S = os.path.join(W, "sel")
sys.path.insert(0, D); sys.path.insert(0, os.path.join(ROOT, "Testing", "asm"))
from nanolib import *
N = int(sys.argv[1]) if len(sys.argv) > 1 else 31
shutil.rmtree(S, ignore_errors=True); os.makedirs(S)
rng = random.Random(3); g = G(rng)
progs = list(CORPUS) + [g.program() for _ in range(N)]
for i, s in enumerate(progs): open(f"{S}/p{i:03}.nano", "w").write(s)
sh = lambda c: subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH {c}", shell=True, check=True)
sh(f"NANO_DIR={S} lake env lean --tstack=400000 Testing/nano/emit_nano.lean")
os.chdir(os.path.join(ROOT, "Testing", "asm"))
sys.argv = ["frontx_test.py", "-", "0", "nanoasm"]
import frontx_test as F
F.LISTS.add("nanoasm")
F.check(len(F.CASES))                                            # (a)
rows = [l.split() for l in open(f"{S}/index.txt")]
unhex = lambda h: b"" if h == "-" else bytes.fromhex(h)
cases = [(list(unhex(r[1])), [0] * (len(unhex(r[1])) + 8)) for r in rows]
lay, halt, base, tab, size = F.build(cases, "".join(f"  .word 0x{w:08x}\n" for w in F.words))
mem = F.qemu(halt, base, tab + F.E * len(cases) - base)
subprocess.run(f"riscv64-linux-gnu-gcc -O1 -static -march=rv64g -mabi=lp64d {D}/driver.c -o {W}/driver", shell=True, check=True)
npairs = 0
for c, (r, (i0, o0, w0)) in enumerate(zip(rows, lay)):
    a1 = int.from_bytes(mem[tab - base + F.E * c + 64:][:8], "little")
    code = bytes(mem[o0:o0 + a1])
    assert code == unhex(r[2]), ("binary asm != Lean nanoGen", r[0])
    open(f"{W}/code.bin", "wb").write(code)
    for run in r[3].split(";"):
        a, want = run.split("="); args = [int(x) for x in a.split(",") if x]
        open(f"{W}/args.bin", "wb").write(b"".join(x.to_bytes(8, "little") for x in args) or b"\0")
        got = int.from_bytes(subprocess.run(f"qemu-riscv64 {W}/driver {W}/code.bin {W}/args.bin", shell=True, check=True, capture_output=True).stdout, "little")
        assert got == int(want), (r[0], args, got, want); npairs += 1
print(f"self-hosting: {len(rows)} nano programs: records assembled by the nanoAsm binary on QEMU (== Lean nanoGen); "
      f"{npairs} (program, input) runs of that code on qemu-riscv64 == Prog.eval")
