#!/usr/bin/env python3
"""(b): run the tinyCompile output of tiny programs on qemu-riscv64 (user mode); compare with Lean's `tinyRun`.
Cases from `run.cases` (written by emit_tiny.lean): prog input tinyRun-output code (hex, '-' = empty)."""
import os, subprocess
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "work"); os.makedirs(W, exist_ok=True)
subprocess.run(f"riscv64-linux-gnu-gcc -O1 -static -march=rv64g -mabi=lp64d {D}/driver.c -o {W}/driver", shell=True, check=True)
unhex = lambda h: b"" if h == "-" else bytes.fromhex(h)
n = 0
for l in open(os.path.join(D, "run.cases")):
    prog, inp, want, code = map(unhex, l.split())
    open(f"{W}/code.bin", "wb").write(code); open(f"{W}/in.bin", "wb").write(inp)
    got = subprocess.run(f"qemu-riscv64 {W}/driver {W}/code.bin {W}/in.bin", shell=True, check=True, capture_output=True).stdout
    assert got == want, (prog.hex(), inp.hex(), got.hex(), want.hex())
    n += 1
print(f"{n} (program, input) cases: QEMU(tinyCompile prog) == tinyRun prog")
