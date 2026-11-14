#!/usr/bin/env python3
"""gcd / sum code of apc/test/words.txt: AArch64 QEMU vs the runnable Lean ARM (Sail) model vs Python.
usage: loop_test.py COMPARE_PY ARMRUN WORKDIR [N=300]   (uses arm-exe/compare.py from branch arm-exe)"""
import os, random, subprocess, sys
cmp_py, armrun, W = sys.argv[1:4]; N = int(sys.argv[4]) if len(sys.argv) > 4 else 300
os.makedirs(W, exist_ok=True); M = 2**64
words = dict(l.split(None, 1) for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "words.txt")))
def gcd_sub(a, b):          # gcdSub of Riscv/Examples/LoopExamples.lean
    while a and b:
        if a < b: b -= a
        else: a -= b
    return a | b
r = random.Random(1); out = []
out += ["case gcd", "arm " + words["gcd"].strip()]
for i in range(N):
    a, b = (r.choice([0, 1, 2, 3, 7, 64, 255]), r.randrange(400)) if i % 5 == 0 else (r.randrange(1, 3000), r.randrange(1, 3000))
    if i % 7 == 0: a, b = b, a
    if i % 11 == 0: g = r.randrange(1, 2**40); a, b = g * r.randrange(1, 60), g * r.randrange(1, 60)   # large, few iterations
    out.append(f"t {a:x} {b:x} {r.getrandbits(64):x} {r.getrandbits(64):x} {gcd_sub(a, b):x}")
out += ["case sum", "arm " + words["sum"].strip()]
for i in range(N):
    n, acc = r.randrange(0, 400), r.choice([0, 1, M - 1, r.getrandbits(64)])
    out.append(f"t {n:x} {acc:x} {r.getrandbits(64):x} {r.getrandbits(64):x} {(acc + n * (n + 1) // 2) % M:x}")
open(os.path.join(W, "cases.txt"), "w").write("\n".join(out) + "\n")
sys.exit(subprocess.run([sys.executable, cmp_py, armrun, os.path.join(W, "cases.txt"), os.path.join(W, "w")]).returncode)
