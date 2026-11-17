#!/usr/bin/env python3
"""Stage test (nano-closeA): a compiled nano stage (`expm`: `Nano.Self.nanoExpM` = `mexp`; `lex`: `Nano.Self.lexBE` =
`lexB`) vs executed Lean on the spec function.  Inputs: corpus + R random programs (UInt64 and Int64) + raw byte strings
(random micro-ops for expm; mutated sources and random bytes for lex).  QEMU on every case (bulk); QEMU + Sail on the
first S cases (smoke: frontx_test's full check, incl. Sail write ranges, gp / sp, a1 = length).
usage: stage_test.py expm|lex [R random programs] [S sail cases] [seed], from the repo root"""
import os, random, subprocess, sys, shutil
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", ".."))
sys.path.insert(0, D)
from nanolib import *
ST = sys.argv[1]; R = int(sys.argv[2]) if len(sys.argv) > 2 else 20; S = int(sys.argv[3]) if len(sys.argv) > 3 else 8
rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 7)
W = os.path.join(D, "work", "stage_" + ST); shutil.rmtree(W, ignore_errors=True); os.makedirs(W)
gu, gi = G(rng), GI(rng, "Int64")
srcs = list(CORPUS) + list(INT_CORPUS) + [gu.program() for _ in range(R)] + [gi.program() for _ in range(R)]
for i, s in enumerate(srcs): open(f"{W}/p{i:04}.nano", "w").write(s)
raws = []
if ST == "expm":
    for _ in range(4 * R):
        n = rng.choice([0, 1, 2, 3, 5, 8, 20, 101])
        raws.append(bytes(rng.choice([rng.randrange(16), rng.randrange(256)]) if j % 2 == 0 else rng.randrange(256) for j in range(n)))
else:
    alpha = b"abxyfdeltUIn64 ()*+-;:=\n0123456789_\t#"
    for _ in range(2 * R):
        s = bytearray(rng.choice(srcs).encode())
        for _ in range(rng.randrange(1, 4)):
            if s: s[rng.randrange(len(s))] = rng.choice(alpha)
        raws.append(bytes(s))
    raws += [bytes(rng.randrange(256) for _ in range(rng.randrange(12))) for _ in range(R)] + [b"", b" ", b"def", b"(", b")("]
for i, b in enumerate(raws): open(f"{W}/r{i:04}.bin", "wb").write(b)
subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH NANO_DIR={W} NANO_STAGE={ST} lake env lean --tstack=400000 "
               f"Testing/nano/emit_{ST}.lean", shell=True, check=True)
FN = "nanoexpm" if ST == "expm" else "nanolex"
os.chdir(os.path.join(ROOT, "Testing", "asm"))
sys.argv = ["frontx_test.py", "-", "0", FN]
import frontx_test as F
F.LISTS.add(FN)
try:
    # bulk: QEMU on every case
    cases = F.CASES
    func = "".join(f"  .word 0x{w:08x}\n" for w in F.words)
    for lo in range(0, len(cases), 400):
        chunk = cases[lo:lo + 400]
        lay, halt, base, tab, size = F.build(chunk, func)
        mem = F.qemu(halt, base, tab + F.E * len(chunk) - base)
        for c, ((i0, o0, w0), case) in enumerate(zip(lay, chunk)):
            xs, ys = case[0], case[1]; L, Rn = len(xs), len(ys); WK = F.wkc(case)
            assert list(mem[i0:i0 + L + F.G]) == xs + [0xAA] * F.G, ("input", L)
            assert bytes(mem[o0:o0 + Rn]) == bytes(ys), ("qemu", FN, lo + c, bytes(xs).hex(), bytes(mem[o0:o0 + Rn]).hex(), bytes(ys).hex())
            assert list(mem[o0 + Rn:o0 + Rn + F.G]) == [0xAA] * F.G and list(mem[w0 + WK:w0 + WK + F.G]) == [0xAA] * F.G, "guard"
            e = tab - base + F.E * c
            gp, spo, a1 = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56, 64))
            assert gp == F.MAGIC and spo == base + w0 + WK and a1 == Rn, ("regs", gp, spo, a1, Rn)
    print(f"{FN}: QEMU {len(cases)} cases == Lean (inputs up to {max(len(c[0]) for c in cases)} bytes, "
          f"outputs up to {max(len(c[1]) for c in cases)} bytes, rejected [0]: {sum(c[1] == [0] for c in cases)})")
    # smoke: QEMU + Sail (frontx_test's full check) on the first S cases
    F.check(S)
finally: shutil.rmtree(os.path.join(ROOT, "Testing", "asm", "ctest"), ignore_errors=True)
