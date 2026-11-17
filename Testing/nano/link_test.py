#!/usr/bin/env python3
"""Linker test (nano-int): the binary `Nano.Link.link cf cg` (stub ++ cg ++ cf, `Nano/Link.lean`) on QEMU and on the
Sail C simulator vs executed Lean.  Stages: the compiled assembler twice (`asm ∘ asm` on the records of every corpus
program + N random ones): what is tested is the 18-word stub (work-block split, frame, `jal` to the first stage,
fall-through into the second with the caller's ra / a3 / sp), with the theorem's work space `4 K + 96`.
frontx_test checks: output == Lean, a1 = length, guards, gp / sp restored, every Sail write inside output + work.
usage: link_test.py [N random programs] (seed 5), from the repo root"""
import os, random, subprocess, sys, shutil
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", "..")); S = os.path.join(D, "work", "link")
sys.path.insert(0, D); sys.path.insert(0, os.path.join(ROOT, "Testing", "asm"))
from nanolib import *
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10
shutil.rmtree(S, ignore_errors=True); os.makedirs(S)
rng = random.Random(5); g = G(rng)
for i, s in enumerate(list(CORPUS) + [g.program() for _ in range(N)]): open(f"{S}/p{i:03}.nano", "w").write(s)
subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH NANO_DIR={S} lake env lean --tstack=400000 Testing/nano/emit_link.lean",
               shell=True, check=True)
os.chdir(os.path.join(ROOT, "Testing", "asm"))
sys.argv = ["frontx_test.py", "-", "0", "nanolink"]
import frontx_test as F
F.LISTS.add("nanolink")
try: F.check(len(F.CASES))
finally: shutil.rmtree(os.path.join(ROOT, "Testing", "asm", "ctest"), ignore_errors=True)
