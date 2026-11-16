#!/usr/bin/env python3
"""FUZZ10 sanity: the Lean reference (ref10.lean) reproduces the committed Testing/asm/frontx-words/<fn>.cases.
usage: xcheck10.py FN...   (runs lake env lean once per call; needs FZ tmp dir in env FZ_W)"""
import os, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.join(D, "..", "..", "..")
WD = os.path.join(ROOT, "Testing", "asm", "frontx-words")
W = os.path.join(D, "work" + os.environ.get("WSUF", "")); os.makedirs(W, exist_ok=True)
def lean(lines):
    open(f"{W}/x.in", "w").write("\n".join(lines) + "\n")
    env = dict(os.environ, FZ_IN=f"{W}/x.in", FZ_OUT=f"{W}/x.out")
    p = subprocess.run("lake env lean Testing/asm/fuzz10/ref10.lean", shell=True, cwd=ROOT, env=env, capture_output=True, text=True)
    assert p.returncode == 0 and "error" not in p.stdout + p.stderr, (p.stdout + p.stderr)[-2000:]
    out = open(f"{W}/x.out").read().split("\n")[:-1]; assert len(out) == len(lines); return out
bad = 0; tot = 0
for fn in sys.argv[1:]:
    rows = [l.split() for l in open(f"{WD}/{fn}.cases") if l.strip()]
    ins = [r[0] for r in rows]; outs = [r[1] for r in rows]
    got = lean([f"{fn} {x}" for x in ins])
    for x, y, g in zip(ins, outs, got):
        tot += 1
        if y != g: bad += 1; print("MISMATCH", fn, x, "committed", y, "lean", g)
    print(fn, len(rows), "cases checked")
print("total", tot, "mismatches", bad)
