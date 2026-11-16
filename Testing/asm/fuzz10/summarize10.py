#!/usr/bin/env python3
"""FUZZ10: one line per entry from results/{seed21,seed22,big,sail}.txt (cases, failures)."""
import re, os
D = os.path.dirname(os.path.abspath(__file__)); R = os.path.join(D, "results")
ent = open(os.path.join(D, "ALL.txt")).read().split()
rows = {e: {} for e in ent}
for mode in ["seed21", "seed22", "big", "sail"]:
    p = os.path.join(R, mode + ".txt")
    if not os.path.exists(p): continue
    for l in open(p):
        m = re.match(r"(\w+): (\d+) cases ok on (\w+) .*?max input (\d+) B", l)
        if m:
            fr = re.search(r"max written fraction ([\d.]+)", l); pn = re.search(r"PANIC.*?x(\d+)", l)
            rows[m.group(1)][mode] = (int(m.group(2)), int(m.group(4)), fr.group(1) if fr else "-", pn.group(1) if pn else "-")
        elif "FAIL" in l or "Error" in l:
            rows.setdefault("?", {})[mode] = l.strip()[:200]
wi = os.path.join(R, "wa_int_rerun.txt")
if os.path.exists(wi):
    for l in open(wi):
        m = re.match(r"(\w+): (\d+) cases ok on (\w+) \(seed (\d+);.*?max input (\d+) B", l)
        if m: rows[m.group(1)][f"seed{m.group(4)}"] = (int(m.group(2)), int(m.group(5)), None, None)
for e in ent:
    print("|", e, "|", " | ".join(str(rows[e].get(k, "-")) for k in ["seed21", "seed22", "big", "sail"]), "|")
