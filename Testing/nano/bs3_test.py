#!/usr/bin/env python3
"""Tests of the S3-compiled expander `Nano.XS.ExpS3` (`mexp`) and assembler `Nano.AS.AsmS3` (`asm`) (branch
nano-s3-all), compiled code = `Ir.compile (S3.lowerP P)`, against the SPEC functions executed in Lean
(`Testing/nano/emit_bs3.lean`).  Inputs: corpus + R random UInt64 / Int64 programs + mutated sources (expander:
`inlB (stage2 (lexB src))`; assembler: `mexp` of that) + raw inputs (random micro-op strings for the expander, random
records, including non-nano ops and odd lengths, for the assembler).  Bulk: QEMU on every case (`NOSAIL=1 ir_test.py`, work = memoryNeeded and
memoryNeeded - 1, a1 = result length); smoke: QEMU + Sail on the first S cases (Sail write ranges).
usage (repo root): python3 Testing/nano/bs3_test.py [R] [S] [seed]"""
import os, random, subprocess, sys, shutil
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", ".."))
sys.path.insert(0, D)
from nanolib import *
R = int(sys.argv[1]) if len(sys.argv) > 1 else 20; S = int(sys.argv[2]) if len(sys.argv) > 2 else 6
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 7)
W = os.path.join(D, "work", "bs3"); shutil.rmtree(W, ignore_errors=True); os.makedirs(W)
gu, gi = G(rng), GI(rng, "Int64")
srcs = list(CORPUS) + list(INT_CORPUS) + [gu.program() for _ in range(R)] + [gi.program() for _ in range(R)]
alpha = b"abxyfdeltUIn64 ()*+-;:=\n0123456789_\t#"
for _ in range(R):
    s = bytearray(rng.choice(srcs).encode())
    for _ in range(rng.randrange(1, 4)):
        if s: s[rng.randrange(len(s))] = rng.choice(alpha)
    srcs.append(s.decode("latin-1"))
for i, s in enumerate(srcs): open(f"{W}/a{i:04}.nano", "wb").write(s.encode("latin-1"))
ops = [0, 1, 3, 4, 5, 6, 7, 8, 11, 14, 16, 24, 32, 40, 48]
for i in range(2 * R):
    n = rng.choice([0, 1, 2, 3, 5, 8, 20, 101])
    open(f"{W}/c{i:04}.mx", "wb").write(bytes(rng.choice([rng.randrange(13), rng.randrange(256)]) if j % 2 == 0
                                              else rng.randrange(256) for j in range(n)))
for i in range(2 * R):
    n = rng.choice([0, 1, 3, 4, 7, 8, 40, 400])
    open(f"{W}/d{i:04}.as", "wb").write(bytes(rng.choice(ops + [rng.randrange(256)]) if j % 4 == 0
                                              else rng.randrange(256) for j in range(n)))
subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH NANO_DIR={W} lake env lean --tstack=4000000 "
               f"Testing/nano/emit_bs3.lean", shell=True, check=True)
STAGES = [("exp", "nano_exp"), ("asm", "nano_asm")]
A = os.path.join(ROOT, "Testing", "asm")
try:
    for _, nm in STAGES:
        n = sum(1 for l in open(os.path.join(A, "ir-words", nm + ".cases")) if l.strip())
        subprocess.run(f"cd {A} && NOSAIL=1 python3 ir_test.py check {n} {nm}", shell=True, check=True)
        subprocess.run(f"cd {A} && python3 ir_test.py check {S} {nm}", shell=True, check=True)
finally:
    shutil.rmtree(os.path.join(A, "ctest"), ignore_errors=True)
