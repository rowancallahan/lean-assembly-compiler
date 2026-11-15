#!/usr/bin/env python3
"""report.py out.txt -> table of F<n>, function, status, first lines of the exact message (Orig.lean attempts)"""
import re, sys
src = open("Orig.lean").read().split("\n")
att = {}   # command line (1-based) -> (F, fn)
for i, l in enumerate(src):
    m = re.match(r"-- (F\d+)$", l)
    if m: att[i + 2] = (m.group(1), src[i + 1].split()[1])
res = {}
cur = None
for l in open(sys.argv[1]):
    if re.match(r"(/root|backtrace|PANIC)", l) or "libleanshared" in l: 
        if l.startswith("PANIC") and cur: res[cur].append(l.rstrip())
        continue
    m = re.match(r"Testing/leansvg/Orig.lean:(\d+):\d+: (error|warning): (.*)", l)
    if m:
        cur = att[int(m.group(1))][0]; res.setdefault(cur, []).append(m.group(3)); continue
    m = re.match(r"frontx: (\S+?)[: ]", l)
    if m:
        name = m.group(1).replace("LeanSvgOrig.", "")
        cur = next(f for f, fn in att.values() if fn == name); res.setdefault(cur, []).append("OK " + l.rstrip()[:70]); continue
    if cur and l.strip(): res[cur].append(l.rstrip())
for ln, (f, fn) in sorted(att.items()):
    r = res.get(f, ["(no message)"])
    ok = r[0].startswith("OK") and not any(x.startswith(("frontx:", "No goals", "unsupported")) or "error" in x[:6] for x in r[1:] if not x.startswith("OK"))
    print(f"{f}\t{fn}\t{'ACCEPTED' if ok else 'REJECTED'}\t" + " / ".join(x.strip() for x in r[:3] if x.strip())[:230])
