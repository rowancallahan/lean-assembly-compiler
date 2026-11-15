#!/usr/bin/env python3
"""Self-hosting data point: the front-end binary of `tinyCompile` (`frontx-words/tinycompile.words`, machine theorem
`tinyCompile.implements1`) compiles the tiny programs of `run.cases` on qemu-system-riscv64; each code it returns
(length from a1) is then run on qemu-riscv64 (`driver.c`) on every input and compared with Lean's `tinyRun`; the code
is also compared with Lean's `tinyCompile`. No Lean in the loop: tiny program -> RISC-V code by the compiled compiler."""
import os, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "work"); os.makedirs(W, exist_ok=True)
sys.argv = ["frontx_test.py", "-", "0", "tinycompile"]
sys.path.insert(0, os.path.dirname(D))
import frontx_test as F
unhex = lambda h: b"" if h == "-" else bytes.fromhex(h)
rows = [tuple(map(unhex, l.split())) for l in open(os.path.join(D, "run.cases")) if l.strip()]
progs = list(dict.fromkeys(r[0] for r in rows))
# output buffers larger than needed; the binary returns the length in a1
lay, halt, base, tab, size = F.build([(list(p), [0] * (4 * len(p) + 8)) for p in progs],
                                     "".join(f"  .word 0x{w:08x}\n" for w in F.words))
mem = F.qemu(halt, base, tab + F.E * len(progs) - base)
code = {}
for c, (p, (i0, o0, w0)) in enumerate(zip(progs, lay)):
    a1 = int.from_bytes(mem[tab - base + F.E * c + 64:][:8], "little")
    code[p] = bytes(mem[o0:o0 + a1])
subprocess.run(f"riscv64-linux-gnu-gcc -O1 -static -march=rv64g -mabi=lp64d {D}/driver.c -o {W}/driver", shell=True, check=True)
n = 0
for prog, inp, want, lean_code in rows:
    assert code[prog] == lean_code, ("binary tinyCompile != Lean tinyCompile", prog.hex())
    open(f"{W}/code.bin", "wb").write(code[prog]); open(f"{W}/in.bin", "wb").write(inp)
    got = subprocess.run(f"qemu-riscv64 {W}/driver {W}/code.bin {W}/in.bin", shell=True, check=True, capture_output=True).stdout
    assert got == want, (prog.hex(), inp.hex(), got.hex(), want.hex())
    n += 1
print(f"self-hosting: {len(progs)} tiny programs compiled by the tinyCompile binary on QEMU (== Lean tinyCompile); "
      f"{n} (program, input) runs of its output on qemu-riscv64 == Lean tinyRun")
