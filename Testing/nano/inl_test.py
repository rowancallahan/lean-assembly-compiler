#!/usr/bin/env python3
"""Inliner stage test (nano-closeB): the compiled paged inliner (`Nano.IP.inlP.pg.body`, theorem
`Nano.IP.inlP_implements`) on QEMU and on the Sail C simulator vs executed Lean `inlB (serU u)`, for the corpus +
N random programs, work block 8192 * 601 bytes.  frontx_test checks: output == Lean, a1 = length, guards, gp / sp
restored, every Sail write inside output + work.
usage: inl_test.py [N random programs] [first M cases] (seed 9), from the repo root"""
import os, random, subprocess, sys, shutil
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", "..")); S = os.path.join(D, "work", "inl")
sys.path.insert(0, D); sys.path.insert(0, os.path.join(ROOT, "Testing", "asm"))
from nanolib import *
N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
M = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 6
shutil.rmtree(S, ignore_errors=True); os.makedirs(S)
rng = random.Random(9); g = G(rng)
for i, s in enumerate(list(CORPUS) + [g.program() for _ in range(N)]): open(f"{S}/p{i:03}.nano", "w").write(s)
subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH NANO_DIR={S} lake env lean --tstack=4000000 Testing/nano/emit_inl.lean",
               shell=True, check=True)
os.chdir(os.path.join(ROOT, "Testing", "asm"))
sys.argv = ["frontx_test.py", "-", "0", "nanoinl"]
import frontx_test as F
try: F.check(min(M, len(F.CASES)))
finally: shutil.rmtree(os.path.join(ROOT, "Testing", "asm", "ctest"), ignore_errors=True)
