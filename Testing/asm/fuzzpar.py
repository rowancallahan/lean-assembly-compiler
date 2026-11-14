#!/usr/bin/env python3
"""usage: fuzzpar.py cases.txt [J]  -- split cases round-robin over J parallel triple.py runs (separate WORK dirs), fail if any fails."""
import os, subprocess, sys, tempfile
f, J = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else os.cpu_count()
T = os.path.join(os.path.dirname(os.path.abspath(__file__)), "triple.py"); d = tempfile.mkdtemp(); parts = [[] for _ in range(J)]; i = -1
for l in open(f):
    if l.startswith("case"): i += 1
    parts[i % J].append(l)
ps = []
for j, ls in enumerate(parts):
    open(f"{d}/{j}.txt", "w").writelines(ls)
    ps.append(subprocess.Popen([sys.executable, T, f"{d}/{j}.txt"], env={**os.environ, "WORK": f"{d}/w{j}"}, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True))
bad = 0
for p in ps:
    o, e = p.communicate(); bad += p.returncode != 0
    print(o, end=""); print("\n".join(x for x in e.splitlines() if "RWX" not in x), file=sys.stderr)
sys.exit(bad)
