#!/usr/bin/env python3
"""Find the first def of the stripped self_S source whose prefix (plus a stub main) B1 compiles to an EMPTY output (parser or g41 rejects).  usage: bisect_g41.py src.txt B1"""
import re, subprocess, sys
t = open(sys.argv[1]).read(); B = sys.argv[2]
parts = re.split(r'\n(?=def )', t.strip('\n')); assert parts[-1].startswith("def m "); defs = parts[:-1]
stub = "def m (x : List UInt8) : List UInt8 := put [] 0\n"
def run(k): return len(subprocess.run([B], input=("\n".join(defs[:k]) + "\n" + stub).encode(), capture_output=True).stdout)
lo, hi = 0, len(defs)
if run(hi) > 0: print("whole source (without driver) compiles:", run(hi), "bytes"); sys.exit(0)
while lo + 1 < hi:
    mid = (lo + hi) // 2
    if run(mid) > 0: lo = mid
    else: hi = mid
print("first failing prefix length", hi, "of", len(defs), "; last def added:", defs[hi - 1][:300].replace("\n", " "))
