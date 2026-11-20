#!/usr/bin/env python3
"""Compares two per-word profiles of the compiler (B2) on two inputs of different size, by function region (regions as in
profile_regions.py: jal-ra targets of B2). Prints regions sorted by instructions at the larger size, with the growth factor,
calls, and instructions per call at each size. A factor near (K2/K1)^2 means quadratic growth, near K2/K1 linear.
usage: profile_growth.py B2.bin PROF_SMALL PROF_LARGE RATIO_K N=25"""
import struct, sys
code, ps, pl, rk = sys.argv[1], sys.argv[2], sys.argv[3], float(sys.argv[4])
N = int(sys.argv[5]) if len(sys.argv) > 5 else 25
w = struct.unpack("<%dI" % (len(open(code, "rb").read()) // 4), open(code, "rb").read())
A = struct.unpack("<%dQ" % len(w), open(ps, "rb").read()); B = struct.unpack("<%dQ" % len(w), open(pl, "rb").read())
ents = {0}
for i, x in enumerate(w):
    if x & 0x7f == 0x6f and (x >> 7) & 31 == 1:
        imm = ((x >> 31) << 20) | (((x >> 12) & 0xff) << 12) | (((x >> 20) & 1) << 11) | (((x >> 21) & 0x3ff) << 1)
        imm = imm - (1 << 21) if imm >> 20 else imm
        ents.add(i + imm // 4)
ents = sorted(ents)
rows = []
for k, e in enumerate(ents):
    hi = ents[k + 1] if k + 1 < len(ents) else len(w)
    a, b = sum(A[e:hi]), sum(B[e:hi])
    if b == 0: continue
    rows.append((b, e, hi - e, A[e], B[e], a, b))
ta, tb = sum(A), sum(B)
print(f"total instructions: small {ta}, large {tb}, factor {tb/ta:.2f} (K ratio {rk}, linear {rk:.1f}, quadratic {rk*rk:.1f})")
print("entry  size  calls_small  calls_large  instr_small  instr_large  factor  instr/call_small  instr/call_large  share_large")
for b, e, sz, ca, cb, a, bb in sorted(rows, reverse=True)[:N]:
    f = bb / a if a else float('inf')
    print(f"{e:6d} {sz:5d} {ca:12d} {cb:12d} {a:12d} {bb:12d} {f:7.2f} {a/ca if ca else 0:16.1f} {bb/cb:16.1f} {100*bb/tb:10.2f}%")
