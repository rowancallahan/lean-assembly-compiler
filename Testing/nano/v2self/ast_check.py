#!/usr/bin/env python3
"""Well-formedness + WIDTH check of a Par1 AST dump (8-byte LE words).  Counts defs/nodes per tag and reports violations of: every def consumed exactly, ids 0.. in order,
CALL total argument width = callee npw, CONTINUE width = npw-1 of its def, IF branch widths equal, LET value width = w, LOOP arm widths = nres, def body width = nres, PRIM args width 1.
usage: ast_check.py O.bin  (exit 1 on any violation)"""
import struct, sys, collections
d = open(sys.argv[1], 'rb').read(); w = struct.unpack('<%dQ' % (len(d) // 8), d)
PA = {1: 0, 2: 1, 3: 0, 4: 2, 5: 0, 6: 1, 7: 2, 8: 3, 9: 2}
i = 1; cnt = collections.Counter(); nd = 0; defs = []; bad = []; cur = None
assert w[0] == 2
def node():
    """returns the width of the expression"""
    global i, nd
    t = w[i]; i += 1; nd += 1; cnt[t] += 1
    if t == 1: i += 1; return 1
    if t == 2: ww = w[i + 1]; i += 2; return ww
    if t == 3: i += 1; a = node(); b = node(); (a == 1 and b == 1) or bad.append(("BIN widths", cur, a, b)); return 1
    if t == 4:
        i += 1; a = node(); b = node(); x = node(); y = node()
        (a == 1 and b == 1) or bad.append(("IF cond widths", cur, a, b))
        if x is None: return y
        if y is None: return x
        x == y or bad.append(("IF branch widths", cur, x, y)); return x
    if t == 5:
        slot, ww = w[i], w[i + 1]; i += 2; v = node(); b = node(); v == ww or bad.append(("LET value width", cur, v, ww)); return b
    if t == 6:
        n = w[i]; i += 1; return sum(node() for _ in range(n))
    if t == 8:
        cid, n = w[i], w[i + 1]; i += 2; tot = sum(node() for _ in range(n))
        if cid >= len(defs): bad.append(("CALL to a later def", cur, cid)); return 1
        tot == defs[cid][0] or bad.append(("CALL arg width", cur, "callee", cid, tot, "!=", defs[cid][0])); return defs[cid][2]
    if t == 9:
        p = w[i]; i += 1
        for _ in range(PA[p]): (node() == 1) or bad.append(("PRIM arg width", cur, p))
        return 1
    if t == 10:
        z = node(); s = node()
        if z is None: return s
        if s is None: return z
        z == s or bad.append(("LOOP arm widths", cur, z, s)); return z
    if t == 11:
        e = node(); e == defs_cur[0] - 1 or bad.append(("CONTINUE width", cur, e, "expected", defs_cur[0] - 1)); return None
    raise Exception(f"bad tag {t} at {i-1}")
while i < len(w):
    assert w[i] == 20, (i, w[i]); assert w[i + 1] == len(defs), ("def id", w[i + 1], len(defs))
    npw, ns, kind, nres = w[i + 2], w[i + 3], w[i + 4], w[i + 5]; i += 6; cur = len(defs); defs_cur = (npw, ns, nres)
    ww = node(); assert w[i] == 21, (i, w[i]); i += 1
    if kind == 0 or True: ww is None or ww == nres or bad.append(("def body width", cur, ww, nres))
    defs.append((npw, ns, nres))
print(f"defs {len(defs)}, nodes {nd}, words {len(w)}, by tag {dict(sorted(cnt.items()))}")
print(f"width violations: {len(bad)}", *bad[:10], sep="\n  ")
sys.exit(1 if bad else 0)
