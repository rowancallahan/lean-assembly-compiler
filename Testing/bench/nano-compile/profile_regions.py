#!/usr/bin/env python3
"""Per-function instruction profile of a RISC-V code file from a nanorun NANORUN_PROF dump.
Function regions = the call targets of `jal ra` (each is a function entry: prologue `addi x31,x31,-8`), sorted by address;
a word belongs to the last entry at or below it. Prints the top N regions: entry word, size in words, calls (executions of the
entry word), executed instructions and share, and the share of loads/stores/branches among them.
usage: profile_regions.py CODE.bin PROF.bin [N=20] [TOTAL_INSTR]"""
import struct, sys
code, prof = sys.argv[1], sys.argv[2]
N = int(sys.argv[3]) if len(sys.argv) > 3 else 20
w = struct.unpack("<%dI" % (len(open(code, "rb").read()) // 4), open(code, "rb").read())
p = struct.unpack("<%dQ" % len(w), open(prof, "rb").read())
ents = set([0])
for i, x in enumerate(w):
    if x & 0x7f == 0x6f and (x >> 7) & 31 == 1:
        imm = ((x >> 31) << 20) | (((x >> 12) & 0xff) << 12) | (((x >> 20) & 1) << 11) | (((x >> 21) & 0x3ff) << 1)
        imm = imm - (1 << 21) if imm >> 20 else imm
        ents.add(i + imm // 4)
ents = sorted(ents)
total = sum(p)
reg = []
for k, e in enumerate(ents):
    hi = ents[k + 1] if k + 1 < len(ents) else len(w)
    n = sum(p[e:hi])
    if n == 0: continue
    ops = [w[i] & 0x7f for i in range(e, hi) for _ in [0]]
    ld = sum(p[i] for i in range(e, hi) if w[i] & 0x7f == 0x03)
    st = sum(p[i] for i in range(e, hi) if w[i] & 0x7f == 0x23)
    br = sum(p[i] for i in range(e, hi) if w[i] & 0x7f == 0x63)
    reg.append((n, e, hi - e, p[e], ld, st, br))
print(f"regions (function entries) executed: {len(reg)} of {len(ents)}; total instructions {total}")
print(" rank  entry_word  size  calls      instructions   share   load%  store%  branch%")
for r, (n, e, sz, calls, ld, st, br) in enumerate(sorted(reg, reverse=True)[:N], 1):
    print(f"{r:5d} {e:11d} {sz:5d} {calls:9d} {n:15d} {100*n/total:6.2f}% {100*ld/n:6.1f}% {100*st/n:6.1f}% {100*br/n:6.1f}%")
