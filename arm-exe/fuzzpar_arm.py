#!/usr/bin/env python3
"""usage: fuzzpar_arm.py ARMRUN cases.txt [J]  -- split cases round-robin over J parallel compare.py runs; prints their output and a grand total."""
import os, re, subprocess, sys, tempfile, time
armrun, f = sys.argv[1:3]; J = int(sys.argv[3]) if len(sys.argv) > 3 else os.cpu_count()
C = os.path.join(os.path.dirname(os.path.abspath(__file__)), "compare.py"); d = tempfile.mkdtemp(); parts = [[] for _ in range(J)]; i = -1
for l in open(f):
    if l.startswith("case"): i += 1
    parts[i % J].append(l)
t0 = time.time(); ps = []
for j, ls in enumerate(parts):
    open(f"{d}/{j}.txt", "w").writelines(ls)
    ps.append(subprocess.Popen([sys.executable, C, armrun, f"{d}/{j}.txt", f"{d}/w{j}"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True))
n = bad = fail = 0
for q in ps:
    o, e = q.communicate(); fail += q.returncode != 0
    print("\n".join(x for x in o.splitlines() if x.startswith(("MISMATCH", "TOTAL")))); print("\n".join(x for x in e.splitlines() if "RWX" not in x), file=sys.stderr)
    m = re.search(r"TOTAL (\d+) inputs, \d+ cases, mismatches (\d+)", o); n += int(m.group(1)); bad += int(m.group(2))
dt = time.time() - t0
print(f"GRAND TOTAL {f}: {i + 1} cases, {n} pairs, mismatches {bad}, {dt:.0f} s wall with {J} procs = {n/dt:.0f} pairs/s; model == expected == QEMU: {bad == 0 and fail == 0}")
sys.exit(fail)
