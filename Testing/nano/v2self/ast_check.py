#!/usr/bin/env python3
"""Well-formedness walk of a Par1 AST dump (8-byte LE words): counts defs/nodes per tag, checks every def is consumed exactly and ids are 0.. in order.
usage: ast_check.py O.bin"""
import struct, sys, collections
w = struct.unpack('<%dQ' % (len(open(sys.argv[1], 'rb').read()) // 8), open(sys.argv[1], 'rb').read())
PA = {1: 0, 2: 1, 3: 0, 4: 2, 5: 0, 6: 1, 7: 2, 8: 3, 9: 2}
i = 0; cnt = collections.Counter(); nd = 0
assert w[0] == 2; i = 1
def node():
    global i, nd
    t = w[i]; i += 1; nd += 1; cnt[t] += 1
    if t == 1: i += 1
    elif t == 2: i += 2
    elif t == 3: i += 1; node(); node()
    elif t == 4: i += 1; [node() for _ in range(4)]
    elif t == 5: i += 2; node(); node()
    elif t == 6: n = w[i]; i += 1; [node() for _ in range(n)]
    elif t == 8: n = w[i + 1]; i += 2; [node() for _ in range(n)]
    elif t == 9: p = w[i]; i += 1; [node() for _ in range(PA[p])]
    elif t == 10: node(); node()
    elif t == 11: node()
    else: raise Exception(f"bad tag {t} at {i-1}")
defs = 0
while i < len(w):
    assert w[i] == 20, (i, w[i]); assert w[i + 1] == defs; i += 6
    node(); assert w[i] == 21, (i, w[i]); i += 1; defs += 1
print(f"defs {defs}, nodes {nd}, words {len(w)}, by tag {dict(sorted(cnt.items()))}")
