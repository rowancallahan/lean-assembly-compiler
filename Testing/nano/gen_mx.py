#!/usr/bin/env python3
"""Generates the record table of `Nano.MX.mx` (Legacy/Nano/ExpandM.lean, Legacy/Nano/ExpandMSelf.lean) from `mexp`'s arms
(Legacy/Nano/Expand.lean): per micro-op m and record number k a UInt64 code (bytes 0-3; bit 32: byte 3 is the argument x,
bit 33: byte 0 is x, bit 34: last record).  `python3 gen_mx.py LEAF` prints the decision tree on (m, k) with every
leaf `LEAF (code)`; m and k are the names `m`, `k` (the view side substitutes `B[i]` for `m`)."""
import sys
X = -1
arms = {0: [[5, 31, 2, 3], [1, 31, 31, 3], [0, 28, 10, 0]], 1: [[4, 5, 28, 7]], 2: [[1, 5, 5, 8], [4, 6, 28, X], [14, 5, 5, 6]],
        3: [[0, 31, 31, 248], [7, 0, 31, 12], [0, 10, 0, 255], [48, 0, 1, 0], [11, 5, 31, 0]], 4: [[8, 28, 28, 1]], 5: [[0, 5, 0, 0]],
        6: [[1, 5, 5, 8], [6, 5, 5, X]], 7: [[3, 5, 31, X]], 8: [[3, 6, 31, 0], [3, 5, 31, 1], [8, 31, 31, 1], [X, 5, 5, 6], [11, 5, 31, 0]],
        9: [[3, 5, 31, 0], [8, 31, 31, X], [11, 5, 31, 0]], 10: [[5, 6, 5, X]], 11: [[16, 6, 13, X]], 12: [[48, 0, 1, 0]]}
def code(r, last):
    c = 0; f = 0
    for j, b in enumerate(r):
        if b == X: f |= (2 if j == 0 else 1); assert j in (0, 3)
        else: c |= b << (8 * j)
    return c | (f << 32) | ((4 if last else 0) << 32)
def tree(M, LEAF):
    def arm(m):
        rs = arms[m]
        s = "".join(f"if k == {k} then {LEAF} (0x{code(r, False):X} : UInt64) else " for k, r in enumerate(rs[:-1]))
        return "(" + s + f"{LEAF} (0x{code(rs[-1], True):X} : UInt64))"
    ch = lambda ms, d: "(" + "".join(f"if {M} == {m} then {arm(m)} else " for m in ms) + arm(d) + ")"
    return f"(if {M} < 6 then {ch(range(5), 5)} else if {M} < 12 then {ch(range(6, 11), 11)} else {arm(12)})"
if __name__ == "__main__":
    print(tree(sys.argv[2] if len(sys.argv) > 2 else "m", sys.argv[1]))
    # self-check against mexp's arms: decode every leaf
    for m, rs in arms.items():
        for k, r in enumerate(rs):
            c = code(r, k == len(rs) - 1); x = 0xEE
            b = [x if c >> 33 & 1 else c & 255, c >> 8 & 255, c >> 16 & 255, x if c >> 32 & 1 else c >> 24 & 255]
            assert b == [x if v == X else v for v in r] and (c >> 34 & 1) == (k == len(rs) - 1)
