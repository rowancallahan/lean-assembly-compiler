#!/usr/bin/env python3
"""classify_ind.py: share of the steady-state instructions per node (work/trace_<fn>.txt from trace_ind.py) by cause:
ladder = constants built bit by bit (`li r,0` then `slli r,r,1` / `addi r,r,1`...), slot = ld/sd with gp base (variables in frame slots),
move = `add rd,zero,rs`, rest."""
import re, os, sys
D = os.path.dirname(os.path.abspath(__file__))
for fn in ["count", "mirror", "nontail", "reverse", "append", "hasparam"]:
    L = []
    for l in open(os.path.join(D, "work", f"trace_{fn}.txt")):
        m = re.match(r"\s*([0-9a-f]+) x([\d.]+)\s+(.*)", l); L.append((int(m.group(1), 16), float(m.group(2)), m.group(3).strip().replace("\t", " ")))
    c = {"ladder": 0, "slot": 0, "move": 0, "rest": 0}; reg = None
    for i, (pc, v, t) in enumerate(L):
        m = re.match(r"li (\w+),0$", t)
        if m: reg = m.group(1); c["ladder"] += v; continue
        if reg and (t == f"slli {reg},{reg},0x1" or t == f"addi {reg},{reg},1"): c["ladder"] += v; continue
        reg = None
        if re.match(r"[ls][dwb] \w+,-?\d+\(gp\)", t): c["slot"] += v
        elif re.match(r"add \w+,zero,\w+$", t): c["move"] += v
        else: c["rest"] += v
    tot = sum(c.values()); print(f"{fn:9s} {tot:7.1f}/node  " + "  ".join(f"{k} {v:6.1f} ({100*v/tot:2.0f}%)" for k, v in c.items()))
