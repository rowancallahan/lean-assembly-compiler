#!/usr/bin/env python3
"""Integrator helper (nano-int): regenerate the nano tail of Testing/scripts/expected-axioms.txt from the actual
`#print axioms` output of axioms_nano-{e2e,proof,mvp,int}.lean (check.sh's order and formatting), after CHECKING every
line: the axiom list is exactly the Sail set (taken from a non-nano machine theorem already in the file) or a subset
of {propext, Classical.choice, Quot.sound}.  Anything else aborts."""
import os, re, subprocess, sys
R = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
P = f"{R}/Testing/scripts/expected-axioms.txt"
old = [l for l in open(P).read().split("\n") if l]
head = [l for l in old if not l.startswith("'Nano")]
ax = lambda l: l.split("dependsonaxioms:")[1] if "dependsonaxioms:" in l else None
sail = max((ax(l) for l in head if ax(l)), key=len)
assert sail.count(",") >= 70 and "sorryAx" not in sail
std = {"propext", "Classical.choice", "Quot.sound"}
new = []
for g in ["nano-e2e", "nano-proof", "nano-mvp", "nano-int"]:
    r = subprocess.run(f"cd {R} && PATH=$HOME/.elan/bin:$PATH lake env lean Testing/scripts/axioms_{g}.lean",
                       shell=True, capture_output=True, text=True)
    assert r.returncode == 0, (g, r.stdout[-2000:], r.stderr[-2000:])
    t = re.sub(r"'Nano", "\n'Nano", r.stdout.replace("\n", "")).replace(" ", "")
    for l in t.split("\n"):
        if not l: continue
        if l.endswith("doesnotdependonanyaxioms"): new.append(l); continue
        a = ax(l); assert a is not None, l
        assert a == sail or set(a.strip("[]").split(",")) <= std, ("UNEXPECTED AXIOMS", l[:300])
        new.append(l)
open(P, "w").write("\n".join(head + new) + "\n")
print(f"{len(new)} nano lines ({sum(ax(l) == sail for l in new if ax(l))} with the Sail set), {len(head)} others kept")
