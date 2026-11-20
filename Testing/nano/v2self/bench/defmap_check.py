#!/usr/bin/env python3
"""Checks the def -> code-entry map of the compiler's code: source defs (self_S.lean, which the compiler reads) with
arguments or function type, in source order, against the entries of cg_map's table (ids in generation order).
Test: a call edge f -> g in the source should show up as `jal ra` from f's code region to g's entry.
usage: defmap_check.py SELF_S.lean CGMAP.out B2.bin [ALIGN_SHIFT]"""
import re, struct, sys
src, cgm, binf = sys.argv[1:4]
L = open(src).read().split("\n")
defs = []  # (name, body text, has_code)
cur = None
for l in L:
    m = re.match(r"def (\S+)\s*(.*)", l)
    if m:
        cur = [m.group(1), m.group(2)]; defs.append(cur)
    elif cur is not None and l.startswith(("  ", "\t")) or (cur is not None and l.strip() == "" and False):
        cur[1] += "\n" + l
    elif cur is not None and l and not l.startswith("--"):
        cur[1] += "\n" + l
def has_code(d):
    head = d[1].split(":=")[0]
    return "(" in head or "→" in head
fun = [d for d in defs if has_code(d)]
names = [d[0] for d in fun]
ent = [int(l.split()[1]) for l in open(cgm) if l.strip() and l.split()[0].isdigit()]
w = struct.unpack("<%dI" % (337856 // 4), open(binf, "rb").read())
def jal_ra_targets(lo, hi):
    out = set()
    for i in range(lo, hi):
        x = w[i]
        if x & 0x7f == 0x6f and (x >> 7) & 31 == 1:
            imm = ((x >> 31) << 20) | (((x >> 12) & 0xff) << 12) | (((x >> 20) & 1) << 11) | (((x >> 21) & 0x3ff) << 1)
            imm = imm - (1 << 21) if imm >> 20 else imm
            out.add(i + imm // 4)
    return out
print("source defs with code:", len(fun), " cg_map entries:", len(ent))
# calls: for each def, the set of other fun-def names used in its body
calls = {}
for d in fun:
    body = d[1].split(":=", 1)[1] if ":=" in d[1] else ""
    calls[d[0]] = {n for n in names if n != d[0] and re.search(r"(?<![\w'])" + re.escape(n) + r"(?![\w'])", body)}
for shift in range(-4, 5):
    ok = tot = 0
    for k, n in enumerate(names):
        j = k + shift
        if not (0 <= j < len(ent) - 1): continue
        tg = jal_ra_targets(ent[j], ent[j + 1])
        for g in calls[n]:
            gk = names.index(g); gj = gk + shift
            if 0 <= gj < len(ent):
                tot += 1; ok += ent[gj] in tg
    print("shift", shift, "edges matched", ok, "of", tot)
