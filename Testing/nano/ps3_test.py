#!/usr/bin/env python3
"""Tests of the S3-compiled nano stages (branch nano-parse-s3): the parser `Nano.PS.Stage2S3` (`stage2`) and the
inliner `Nano.IS.InlS3` (`inlB`), compiled code = `Ir.compile (S3.lowerP P)`, against the SPEC functions executed in
Lean (`Testing/nano/emit_ps3.lean`).  Inputs: corpus + R random UInt64 / Int64 programs + mutated sources (parser:
`lexB src`; inliner: `stage2 (lexB src)` when nonempty) + raw inputs (random token bytes for the parser, random
micro-op strings for the inliner).  Bulk: QEMU on every case (`NOSAIL=1 ir_test.py`, work = memoryNeeded and
memoryNeeded - 1, a1 = result length); smoke: QEMU + Sail on the first S cases (Sail write ranges).
usage (repo root): python3 Testing/nano/ps3_test.py [R] [S] [seed]"""
import os, random, subprocess, sys, shutil
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", ".."))
sys.path.insert(0, D)
from nanolib import *
R = int(sys.argv[1]) if len(sys.argv) > 1 else 20; S = int(sys.argv[2]) if len(sys.argv) > 2 else 6
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 7)
W = os.path.join(D, "work", "ps3"); shutil.rmtree(W, ignore_errors=True); os.makedirs(W)
gu, gi = G(rng), GI(rng, "Int64")
srcs = list(CORPUS) + list(INT_CORPUS) + [gu.program() for _ in range(R)] + [gi.program() for _ in range(R)]
alpha = b"abxyfdeltUIn64 ()*+-;:=\n0123456789_\t#"
for _ in range(R):
    s = bytearray(rng.choice(srcs).encode())
    for _ in range(rng.randrange(1, 4)):
        if s: s[rng.randrange(len(s))] = rng.choice(alpha)
    srcs.append(s.decode("latin-1"))
for i, s in enumerate(srcs): open(f"{W}/a{i:04}.nano", "wb").write(s.encode("latin-1"))
tokb = [0, 1, 2, 3, 4, 5, 6, 40, 41, 42, 43, 45, 58, 59, 61, 97, 98, 120, 48, 49, 57]
for i in range(R):
    n = rng.choice([0, 1, 2, 5, 12, 30])
    open(f"{W}/b{i:04}.p2", "wb").write(bytes([rng.choice([1, 2, rng.randrange(256)])] +
        [rng.choice(tokb) if rng.random() < 0.8 else rng.randrange(256) for _ in range(n)]))
for i in range(2 * R):
    n = rng.choice([0, 1, 2, 3, 5, 8, 20, 101])
    open(f"{W}/c{i:04}.inl", "wb").write(bytes(rng.choice([rng.randrange(16), rng.randrange(256)]) if j % 2 == 0
                                               else rng.randrange(4) for j in range(n)))
subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH NANO_DIR={W} lake env lean --tstack=4000000 "
               f"Testing/nano/emit_ps3.lean", shell=True, check=True)
A = os.path.join(ROOT, "Testing", "asm")
try:
    for nm in ("nano_ps2", "nano_inl"):
        n = sum(1 for l in open(os.path.join(A, "ir-words", nm + ".cases")) if l.strip())
        subprocess.run(f"cd {A} && NOSAIL=1 python3 ir_test.py check {n} {nm}", shell=True, check=True)
        subprocess.run(f"cd {A} && python3 ir_test.py check {S} {nm}", shell=True, check=True)
finally:
    shutil.rmtree(os.path.join(A, "ctest"), ignore_errors=True)
