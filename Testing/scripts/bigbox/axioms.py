#!/usr/bin/env python3
"""axioms.py [--count] LOG...: every `#print axioms` result in the logs must be exactly the standard axioms.
Lean wraps long results over lines, so each log is joined before matching. Exits 1 (and lists the offenders) if any
result names another axiom (sorryAx included) or if the logs hold no result at all. --count prints how many."""
import re, sys
STD = {"propext", "Classical.choice", "Quot.sound"}
count = sys.argv[1] == "--count"
logs = sys.argv[2:] if count else sys.argv[1:]
res = []
for f in logs:
    t = " ".join(open(f, errors="replace").read().split())
    res += [(n, {a.strip() for a in ax.split(",") if a.strip()})
            for n, ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", t)]
    res += [(n, set()) for n in re.findall(r"'([^']+)' does not depend on any axioms", t)]
bad = [(n, sorted(a - STD)) for n, a in res if not a <= STD]
assert res, f"no #print axioms output in {logs}"
for n, a in bad: print(f"NON-STANDARD {n}: {a}")
if count: print(len(res))
sys.exit(1 if bad else 0)
