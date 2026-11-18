#!/usr/bin/env python3
"""Reference check of the parser's AST against Nano/V2/Front.lean's independent typing: per def (in order) kind (fn/loop), parameter WORDS (loop: +1 for the fuel slot) and result words.
usage: ref_check.py AST.bin SIGS.txt   (SIGS from: lean --run Testing/nano/v2self/ref_sigs.lean TEXT > SIGS.txt)   exit 1 on any mismatch"""
import struct, sys
d = open(sys.argv[1], 'rb').read(); w = struct.unpack('<%dQ' % (len(d) // 8), d)
PA = {1: 0, 2: 1, 3: 0, 4: 2, 5: 0, 6: 1, 7: 2, 8: 3, 9: 2}
i = 1; hdr = []
def node():
    global i
    t = w[i]; i += 1
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
while i < len(w): hdr.append(tuple(w[i + 1:i + 6])); i += 6; node(); i += 1
ref = [l.split() for l in open(sys.argv[2])]
bad = 0
for k, (h, r) in enumerate(zip(hdr, ref)):
    name, kind, npw_ref, nres_ref = r[0], int(r[2]), int(r[3]), int(r[4]); _id, npw, ns, kd, nres = h
    if kd != kind or nres != nres_ref or npw != npw_ref + kind:
        bad += 1; print("DIFF def", k, name, "AST", (npw, kd, nres), "ref", (npw_ref + kind, kind, nres_ref))
print(f"AST defs {len(hdr)}, reference defs {len(ref)}, signature mismatches {bad}")
sys.exit(1 if bad or len(hdr) != len(ref) else 0)
