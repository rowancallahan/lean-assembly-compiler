#!/usr/bin/env python3
"""ownership-stage differential: random typed S programs with Buf variables (pargen.py ... own) → B1 `parse` (Par1) →
verdict of C.o41 (B1 `own`) vs the Python model own_ref.py; the fixed aliasing cases vs their expected verdicts.
usage: owndiff.py B1 DIR N SEED   (exit 1 on a fixed-case failure; model disagreements are listed, the model is a reference, not the spec)"""
import subprocess, sys, struct, os, collections
B1, D, N, SEED = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(here, ".."))
import own_ref
M = int(subprocess.run(["python3", f"{here}/pargen.py", D, str(N), SEED, "own"], check=True, capture_output=True, text=True).stdout.split()[-1])
exp = dict((int(a), b) for a, b in (l.split() for l in open(f"{D}/own_expect.txt")))
words = lambda b: list(struct.unpack('<%dQ' % (len(b) // 8), b))
cnt = collections.Counter(); bad = []; fixed_bad = []
for i in range(M):
    src = open(f"{D}/p{i}.txt", "rb").read()
    ast = words(subprocess.run([B1, "parse"], input=src, capture_output=True, check=True).stdout)
    if not ast: cnt["parse-reject"] += 1; continue
    o = words(subprocess.run([B1, "own"], input=src, capture_output=True, check=True).stdout)
    assert not o or o == ast, f"p{i}: o41 output is neither empty nor its input"
    try: ref = own_ref.check(own_ref.decode(ast)) == "ACCEPT"
    except Exception as e: ref = None
    v = "ACCEPT" if o else "REJECT"
    cnt[(v, "model " + ("ACCEPT" if ref else "REJECT"))] += 1
    if ref is not None and ref != bool(o): bad.append((i, v))
    if i in exp and exp[i] != v: fixed_bad.append((i, v, "expected", exp[i]))
for k, c in sorted(cnt.items(), key=str): print(k, c)
print("o41 vs model disagreements:", bad[:20])
print("fixed cases:", len(exp), "failures:", fixed_bad)
sys.exit(1 if fixed_bad else 0)
