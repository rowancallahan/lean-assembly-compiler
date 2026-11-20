#!/usr/bin/env python3
"""differential fuzz: Par1 (native B1 `parse`) vs ParSpec.refParse.  usage: pardiff.py B1 DIR N SEED  (needs lake env for specrun)"""
import subprocess, sys, struct, os, collections
B1, D, N, SEED = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]; N0 = N
here = os.path.dirname(os.path.abspath(__file__))
N = int(subprocess.run(["python3", f"{here}/pargen.py", D, str(N), SEED], check=True, capture_output=True, text=True).stdout.split()[-1])
spec = {}
out = subprocess.run(["lake", "env", "lean", "--tstack=1000000", "--run", f"{here}/specrun.lean", D, str(N)], capture_output=True, text=True, check=True).stdout
for l in out.splitlines():
    i, *r = l.split(); spec[int(i)] = None if r == ["REJECT"] else [int(x) for x in r]
cnt = collections.Counter(); bad = []
for i in range(N):
    src = open(f"{D}/p{i}.txt", "rb").read()
    r = subprocess.run([B1, "parse"], input=src, capture_output=True)
    b = r.stdout; p1 = list(struct.unpack('<%dQ' % (len(b)//8), b)) if r.returncode == 0 and b else None
    s = spec[i]; mut = i % 2 if i < N0 else 0
    k = ("mut" if mut else "gen", "both-accept-equal" if p1 and s and p1 == s else "both-reject" if not p1 and not s else
         "PAR1 ACCEPTS / SPEC REJECTS" if p1 and not s else "PAR1 REJECTS / SPEC ACCEPTS" if s and not p1 else "ACCEPT-BOTH-DIFFER")
    cnt[k] += 1
    if k[1] not in ("both-accept-equal", "both-reject"): bad.append((i, k[1]))
for k, v in sorted(cnt.items()): print(k, v)
print("disagreements:", bad[:20])
