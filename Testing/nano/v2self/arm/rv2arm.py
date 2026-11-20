#!/usr/bin/env python3
"""rv2arm: translate the compiler's RISC-V output (J programs encoded by RvEnc.encJX) to AArch64.
UNPROVEN GLUE: not part of any correctness theorem.  Usage: python3 rv2arm.py prog_rv.bin > prog_arm.bin

Each RV word is decoded back to its J instruction and becomes a fixed block of K = 4 A64 words (padded with
`add x16, x16, #0`), so J index pc is A64 word 4*pc and every branch offset is relocated by x4.
Calling convention (mirrors RV): x0 input, x1 length, x2 work base, x3 output, x4 = work top (RV sp), return to
x30; result: status x0, length x1.  sp is never used.  Link values are ARM addresses (V2: `bl` is the LAST word of its block, so it links
the next block; `jalr x0, 0(r)` = `br r`).  Only the instructions listed in Testing/notes/NANO_V2_ARM.md's minimal set
are emitted, restricted further to NANO_V2_ARM.md §0-min (no ldur/stur, no SP-relative forms, no store of xzr):
movz/movk, add/sub imm+reg, and/orr/eor, lslv/lsrv, madd, cmp, b.cond, cbz, b, bl, br, ldr/str, ldrb/strb.  Anything outside the J encodings, or out of range, fails an assert."""
import struct, sys

K = 4
# RV register -> A64 register.  0 -> xzr (31; only in ALU/compare operand positions), 2 (sp) -> x4 (an ordinary
# register; the host passes the work top in x4).  x16, x17 are scratch; x18 and x19..x29 are never touched.
RMAP = {0: 31, 1: 30, 2: 4, 5: 5, 6: 6, 7: 7, 8: 8, 10: 0, 11: 1, 12: 2, 13: 3, 14: 14, 15: 15,
        28: 12, 29: 13, 30: 10, 31: 11}
ZR, S0, S1 = 31, 16, 17
PAD = 0x91000000 | S0 << 5 | S0                      # add x16, x16, #0

def sx(v, bits): return v - (1 << bits) if v >> (bits - 1) & 1 else v

def decode(w):
    """RV word -> J instruction tuple (only the encodings of RvEnc.encJX)."""
    op, rd, f3, rs1, rs2, f7 = w & 127, w >> 7 & 31, w >> 12 & 7, w >> 15 & 31, w >> 20 & 31, w >> 25
    iimm = sx(w >> 20, 12)
    if op == 0x13 and f3 == 0: return ('addi', rd, rs1, iimm)
    if op == 0x13 and f3 == 1: assert w >> 26 == 0; return ('slli', rd, rs1, w >> 20 & 63)
    if op == 0x13 and f3 == 5: assert w >> 26 == 0; return ('srli', rd, rs1, w >> 20 & 63)
    if op == 0x03 and f3 == 3: return ('ld', rd, rs1, iimm)
    if op == 0x03 and f3 == 4: return ('lbu', rd, rs1, iimm)
    if op == 0x23:
        simm = sx(f7 << 5 | rd, 12)
        assert f3 in (0, 3), hex(w)
        return ('sd' if f3 == 3 else 'sb', rs2, rs1, simm)
    if op == 0x33:
        alu = {(0, 0): 1, (0, 32): 2, (0, 1): 3, (7, 0): 4, (6, 0): 5, (1, 0): 6, (5, 0): 7, (4, 0): 8}
        return ('alu', alu[(f3, f7)], rd, rs1, rs2)
    if op == 0x63:
        o = sx((w >> 31) << 12 | (w >> 7 & 1) << 11 | (w >> 25 & 63) << 5 | (w >> 8 & 15) << 1, 13)
        assert o % 4 == 0
        return ({0: 'beq', 1: 'bne', 6: 'bltu', 7: 'bgeu'}[f3], rs1, rs2, o // 4)
    if op == 0x6f:
        o = sx((w >> 31) << 20 | (w >> 12 & 255) << 12 | (w >> 20 & 1) << 11 | (w >> 21 & 1023) << 1, 21)
        assert o % 4 == 0
        return ('jal', rd, o // 4)
    if op == 0x67:
        assert f3 == 0 and iimm == 0 and rd == 0, hex(w)
        return ('jalr', rd, rs1)
    raise AssertionError('not a J encoding: %08x' % w)

def R(r):
    assert r in RMAP, r
    return RMAP[r]

def N(r):
    """A64 register of RV register r as a base / add-imm operand: never x0 (31 would be sp there)"""
    assert r != 0
    return R(r)

# A64 encodings (64-bit forms)
def movz(d, imm): assert 0 <= imm < 65536; return 0xD2800000 | imm << 5 | d
def movk(d, imm, hw): assert 0 <= imm < 65536; return 0xF2800000 | hw << 21 | imm << 5 | d
def addi(d, n, imm): assert 0 <= imm < 4096 and d != 31 and n != 31; return 0x91000000 | imm << 10 | n << 5 | d
def subi(d, n, imm): assert 0 <= imm < 4096 and d != 31 and n != 31; return 0xD1000000 | imm << 10 | n << 5 | d
def rr(base, d, n, m): assert 31 not in (d, n, m); return base | m << 16 | n << 5 | d
ADD, SUB, AND, ORR, EOR, LSLV, LSRV, MUL = 0x8B000000, 0xCB000000, 0x8A000000, 0xAA000000, 0xCA000000, \
    0x9AC02000, 0x9AC02400, 0x9B004400                                                     # MUL = madd .., x17 (= 0)
def subs(n, m): return rr(0xEB000000, S0, n, m)                                          # subs x16, n, m (sets NZCV)
def ldr(t, n, off): assert off % 8 == 0 and 0 <= off < 32768 and t != 31; return 0xF9400000 | off // 8 << 10 | n << 5 | t
def str_(t, n, off): assert off % 8 == 0 and 0 <= off < 32768 and t != 31; return 0xF9000000 | off // 8 << 10 | n << 5 | t
def ldrb(t, n, off): assert 0 <= off < 4096 and t != 31; return 0x39400000 | off << 10 | n << 5 | t
def strb(t, n, off): assert 0 <= off < 4096 and t != 31; return 0x39000000 | off << 10 | n << 5 | t
def b(o): assert -(1 << 25) <= o < 1 << 25; return 0x14000000 | o & 0x3FFFFFF
def bl(o): assert -(1 << 25) <= o < 1 << 25; return 0x94000000 | o & 0x3FFFFFF
def bcond(c, o): assert -(1 << 18) <= o < 1 << 18; return 0x54000000 | (o & 0x7FFFF) << 5 | c
def cbz(t, o): assert -(1 << 18) <= o < 1 << 18 and t != 31; return 0xB4000000 | (o & 0x7FFFF) << 5 | t
def br(n): assert n != 31; return 0xD61F0000 | n << 5

def Z(r, out):
    """A64 register holding RV register r as an operand: x0 is x17, zeroed once by a leading `movz x17, #0`"""
    if r != 0: return R(r)
    if movz(S1, 0) not in out: out.insert(0, movz(S1, 0))
    return S1

def addr(rs, off, out):
    """x16 := x[rs] + off (add/sub imm); the access then uses [x16, #0]"""
    out.append(addi(S0, N(rs), off) if off >= 0 else subi(S0, N(rs), -off))
    return S0

def block(j, pc):
    out = []
    def rel(target_pc): return target_pc * K - (pc * K + len(out))   # words from the word about to be emitted
    k = j[0]
    if k in ('addi', 'ld', 'lbu', 'sd', 'sb'): assert -2048 <= j[3] < 2048, j   # imm12 (= ArmEnc.armOK)
    if k in ('slli', 'srli'): assert 0 <= j[3] < 64, j
    if k in ('beq', 'bne', 'bltu', 'bgeu'): assert -65535 <= j[3] <= 65535, j     # b.cond / cbz reach
    if k == 'addi':
        _, rd, rs, imm = j
        R(rd); R(rs)                                     # validate (also when rd = x0)
        if rd != 0:
            if rs == 0 and imm >= 0: out.append(movz(R(rd), imm))
            elif rs == 0:                                # 2^64 + imm: low half-word 65536 + imm, the rest 0xFFFF
                out += [movz(R(rd), 65536 + imm), movk(R(rd), 65535, 1), movk(R(rd), 65535, 2), movk(R(rd), 65535, 3)]
            elif imm >= 0: out.append(addi(R(rd), N(rs), imm))
            else: out.append(subi(R(rd), N(rs), -imm))
    elif k in ('ld', 'lbu'):
        _, rd, rs, off = j
        R(rd); N(rs)
        if rd != 0:
            if k == 'ld':
                if off % 8 == 0 and 0 <= off < 32768: out.append(ldr(R(rd), N(rs), off))
                else: out.append(ldr(R(rd), addr(rs, off, out), 0))
            else:
                if 0 <= off < 4096: out.append(ldrb(R(rd), N(rs), off))
                else: out.append(ldrb(R(rd), addr(rs, off, out), 0))
    elif k in ('sd', 'sb'):
        _, r2, rs, off = j
        t = Z(r2, out)                                   # never store xzr: store a zeroed x17
        st = str_ if k == 'sd' else strb
        if (off % 8 == 0 and 0 <= off < 32768) if k == 'sd' else (0 <= off < 4096): out.append(st(t, N(rs), off))
        else: out.append(st(t, addr(rs, off, out), 0))
    elif k == 'alu':
        _, op, rd, a, bb = j
        R(rd); R(a); R(bb)
        if rd != 0:
            if op == 3: Z(0, out)                        # madd's addend: x17 = 0
            out.append(rr({1: ADD, 2: SUB, 3: MUL, 4: AND, 5: ORR, 6: LSLV, 7: LSRV, 8: EOR}[op], R(rd), Z(a, out), Z(bb, out)))
    elif k in ('slli', 'srli'):
        _, rd, rs, sh = j
        R(rd); R(rs)
        if rd != 0:
            n = Z(rs, out)
            out += [movz(S0, sh), rr(LSLV if k == 'slli' else LSRV, R(rd), n, S0)]
    elif k in ('beq', 'bne', 'bltu', 'bgeu'):
        _, a, bb, o = j
        R(a); R(bb)
        if k == 'beq' and a == 0 and bb == 0: out.append(b(rel(pc + o)))
        elif k == 'beq' and (a == 0 or bb == 0): out.append(cbz(R(a if bb == 0 else bb), rel(pc + o)))
        else:
            na, nb = Z(a, out), Z(bb, out)
            out.append(subs(na, nb))
            out.append(bcond({'beq': 0, 'bne': 1, 'bgeu': 2, 'bltu': 3}[k], rel(pc + o)))
    elif k == 'jal':
        _, rd, o = j
        assert rd in (0, 1)
        if rd == 0: out.append(b(rel(pc + o)))
        else:
            while len(out) < K - 1: out.append(PAD)
            out.append(bl(rel(pc + o)))                  # last word: links the next block
    elif k == 'jalr':
        _, rd, rs = j
        assert rs != 0, 'jalr through x0'
        out.append(br(R(rs)))
    else: raise AssertionError(k)
    assert len(out) <= K, (j, out)
    return out + [PAD] * (K - len(out))

def translate(data):
    assert len(data) % 4 == 0
    words = struct.unpack('<%dI' % (len(data) // 4), data)
    js = [decode(w) for w in words]
    for pc, j in enumerate(js):                          # every branch/jump target is inside the code
        if j[0] in ('beq', 'bne', 'bltu', 'bgeu'): assert 0 <= pc + j[3] < len(js)
        if j[0] == 'jal': assert 0 <= pc + j[2] < len(js)
    out = [w for pc, j in enumerate(js) for w in block(j, pc)]
    assert len(out) == K * len(js)
    return struct.pack('<%dI' % len(out), *out)

if __name__ == '__main__':
    assert len(sys.argv) == 2, 'usage: rv2arm.py prog_rv.bin > prog_arm.bin'
    sys.stdout.buffer.write(translate(open(sys.argv[1], 'rb').read()))
