#!/usr/bin/env python3
"""Writes a synthetic RV program (raw words) with the J forms the compiler rarely or never emits: x0 operands, mul,
x2 (sp) operands, far/negative offsets, stores of x0, compare-branches against x0.  Only for comparing the nano
translator with the oracle (it is not meant to run).  UNPROVEN glue.  usage: synth_rv.py > synth.rv"""
import struct, sys
def I(op, f3, rd, rs, imm): return (imm & 4095) << 20 | rs << 15 | f3 << 12 | rd << 7 | op
def S(f3, r2, r1, imm): return ((imm >> 5) & 127) << 25 | r2 << 20 | r1 << 15 | f3 << 12 | (imm & 31) << 7 | 0x23
def R(f7, f3, rd, a, b): return f7 << 25 | b << 20 | a << 15 | f3 << 12 | rd << 7 | 0x33
def B(f3, a, b, o):
    return ((o >> 12) & 1) << 31 | ((o >> 5) & 63) << 25 | b << 20 | a << 15 | f3 << 12 | ((o >> 1) & 15) << 8 | ((o >> 11) & 1) << 7 | 0x63
def J(rd, o): return ((o >> 20) & 1) << 31 | ((o >> 1) & 1023) << 21 | ((o >> 11) & 1) << 20 | ((o >> 12) & 255) << 12 | rd << 7 | 0x6f
ws = []
for (f7, f3) in [(0, 0), (32, 0), (1, 0), (0, 7), (0, 6), (0, 1), (0, 5), (0, 4)]:
    for (a, b) in [(5, 6), (0, 6), (5, 0), (0, 0), (2, 5), (5, 2)]:
        ws.append(R(f7, f3, 7, a, b))
for f3, sh in [(1, 0), (1, 63), (5, 3), (5, 40)]:
    for rs in (0, 2, 5): ws.append(I(0x13, f3, 6, rs, sh))
for rs, imm in [(0, 0), (0, 2047), (0, -1), (0, -2048), (2, -16), (5, 2047), (5, -2048), (2, 8)]:
    ws.append(I(0x13, 0, 5, rs, imm))
for f3 in (3, 4):
    for rs, off in [(8, 0), (8, 8), (8, 12), (8, -8), (8, -2048), (8, 2040), (2, 16), (2, -24)]:
        ws.append(I(3, f3, 5, rs, off))
for f3 in (3, 0):
    for r2, rs, off in [(5, 8, 0), (0, 8, 8), (0, 8, -8), (0, 8, 2047), (5, 2, -2048), (0, 2, 16), (6, 8, 13)]:
        ws.append(S(f3, r2, rs, off))
n0 = len(ws)
for f3 in (0, 1, 6, 7):
    for (a, b) in [(5, 6), (0, 6), (5, 0), (0, 0), (2, 0)]:
        o = -4 * (len(ws) - 1) if len(ws) % 2 else 4 * 3
        ws.append(B(f3, a, b, o))
ws += [J(0, -4 * len(ws)), J(1, 8), I(0x67, 0, 0, 1, 0), I(0x67, 0, 0, 2, 0), I(0x67, 0, 0, 14, 0)]
ws += [I(0x13, 0, 0, 0, 0)] * 4
sys.stdout.buffer.write(struct.pack('<%dI' % len(ws), *ws))
