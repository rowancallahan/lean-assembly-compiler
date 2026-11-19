#!/usr/bin/env python3
"""rv2arm: translate the compiler's RISC-V output (J programs encoded by RvEnc.encJX) to AArch64.
UNPROVEN GLUE: not part of any correctness theorem.  Usage: python3 rv2arm.py prog_rv.bin > prog_arm.bin

Each RV word is decoded back to its J instruction and becomes a fixed block of K = 4 A64 words (padded with
`add x16, x16, #0`), so J index pc is A64 word 4*pc and every branch offset is relocated by x4.
Calling convention (mirrors RV): x0 input, x1 length, x2 work base, x3 output, sp = work top, return to x30;
result: status x0, length x1.  Link values are ARM addresses (V2: `bl` is the LAST word of its block, so it links
the next block; `jalr x0, 0(r)` = `br r`).  Only the instructions listed in Testing/notes/NANO_V2_ARM.md's minimal set
are emitted (movz, add/sub imm+reg, and/orr/eor, lslv/lsrv, madd, subs(cmp), b.cond, b, bl, br, ldr/str/ldur/stur,
ldrb/strb).  Anything outside the J encodings, or out of range, fails an assert."""
import struct, sys

K = 4
# RV register -> A64 register.  0 -> xzr (31 in register-form encodings), 2 (sp) -> sp, handled separately.
# x16, x17 are scratch; x18 is never touched; x19..x29 are never touched (kept).
RMAP = {0: 31, 1: 30, 5: 5, 6: 6, 7: 7, 8: 8, 10: 0, 11: 1, 12: 2, 13: 3, 14: 14, 15: 15,
        28: 12, 29: 13, 30: 10, 31: 11}
SP, ZR, S0, S1 = 2, 31, 16, 17
PAD = 0x91000000 | S0 << 5 | S0                      # add x16, x16, #0

def sx(v, bits): return v - (1 << bits) if v >> (bits - 1) & 1 else v

def decode(w):
    """RV word -> J instruction tuple (only the encodings of RvEnc.encJX)."""
    op, rd, f3, rs1, rs2, f7 = w & 127, w >> 7 & 31, w >> 12 & 7, w >> 15 & 31, w >> 20 & 31, w >> 25
    iimm = sx(w >> 20, 12)
    if op == 0x13 and f3 == 0: return ('addi', rd, rs1, iimm)
    if op == 0x13 and f3 == 1: assert f7 == 0 and rs2 < 32; return ('slli', rd, rs1, w >> 20 & 63)
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
    assert r in RMAP and r != SP, r
    return RMAP[r]

# A64 encodings (64-bit forms)
def movz(d, imm): assert 0 <= imm < 65536; return 0xD2800000 | imm << 5 | d
def addi(d, n, imm): assert 0 <= imm < 4096; return 0x91000000 | imm << 10 | n << 5 | d   # n/d = 31 is sp
def subi(d, n, imm): assert 0 <= imm < 4096; return 0xD1000000 | imm << 10 | n << 5 | d
def rr(base, d, n, m): return base | m << 16 | n << 5 | d                                     # 31 is xzr
ADD, SUB, AND, ORR, EOR, LSLV, LSRV, MUL = 0x8B000000, 0xCB000000, 0x8A000000, 0xAA000000, 0xCA000000, \
    0x9AC02000, 0x9AC02400, 0x9B007C00                                                     # MUL = madd .., xzr
def cmp(n, m): return rr(0xEB000000, 31, n, m)                                           # subs xzr, n, m
def ldr(t, n, off): assert off % 8 == 0 and 0 <= off < 32768; return 0xF9400000 | off // 8 << 10 | n << 5 | t
def str_(t, n, off): assert off % 8 == 0 and 0 <= off < 32768; return 0xF9000000 | off // 8 << 10 | n << 5 | t
def ldur(t, n, off): assert -256 <= off < 256; return 0xF8400000 | (off & 511) << 12 | n << 5 | t
def stur(t, n, off): assert -256 <= off < 256; return 0xF8000000 | (off & 511) << 12 | n << 5 | t
def ldrb(t, n, off): assert 0 <= off < 4096; return 0x39400000 | off << 10 | n << 5 | t
def strb(t, n, off): assert 0 <= off < 4096; return 0x39000000 | off << 10 | n << 5 | t
def b(o): assert -(1 << 25) <= o < 1 << 25; return 0x14000000 | o & 0x3FFFFFF
def bl(o): assert -(1 << 25) <= o < 1 << 25; return 0x94000000 | o & 0x3FFFFFF
def bcond(c, o): assert -(1 << 18) <= o < 1 << 18; return 0x54000000 | (o & 0x7FFFF) << 5 | c
def br(n): return 0xD61F0000 | n << 5

def base(r):
    """A64 base register for an address operand (rn = 31 means sp in imm/load/store forms)."""
    return 31 if r == SP else R(r)

def src(r, scratch, out):
    """A64 register holding RV register r as a register-form operand (sp copied to a scratch first)."""
    if r == SP: out.append(addi(scratch, 31, 0)); return scratch
    return R(r)

def addr(rs, off, out):
    """(base register, residual offset 0) when the offset needs materializing into x16."""
    bs = base(rs)
    if off >= 0: out.append(addi(S0, bs, off))
    else: out.append(subi(S0, bs, -off))
    return S0

def block(j, pc):
    out = []
    def rel(target_pc): return target_pc * K - (pc * K + len(out))   # words from the word about to be emitted
    k = j[0]
    if k == 'addi':
        _, rd, rs, imm = j
        if rd != 0:
            assert rd != SP
            if rs == 0 and imm >= 0: out.append(movz(R(rd), imm))
            elif rs == 0: out += [movz(S0, -imm), rr(SUB, R(rd), ZR, S0)]
            elif imm >= 0: out.append(addi(R(rd), base(rs), imm))
            else: out.append(subi(R(rd), base(rs), -imm))
    elif k in ('ld', 'lbu', 'sd', 'sb'):
        _, r, rs, off = j
        assert rs != 0
        if k in ('ld', 'lbu') and r == 0: pass
        else:
            t = R(r)                                     # sd/sb of x0 store xzr (Rt = 31)
            assert r != SP
            bs = base(rs)
            if k in ('ld', 'sd'):
                if off % 8 == 0 and 0 <= off < 32768: out.append((ldr if k == 'ld' else str_)(t, bs, off))
                elif -256 <= off < 256: out.append((ldur if k == 'ld' else stur)(t, bs, off))
                else: out.append((ldr if k == 'ld' else str_)(t, addr(rs, off, out), 0))
            else:
                if 0 <= off < 4096: out.append((ldrb if k == 'lbu' else strb)(t, bs, off))
                else: out.append((ldrb if k == 'lbu' else strb)(t, addr(rs, off, out), 0))
    elif k == 'alu':
        _, op, rd, a, bb = j
        if rd != 0:
            assert rd != SP
            na, nb = src(a, S0, out), src(bb, S1, out)
            out.append(rr({1: ADD, 2: SUB, 3: MUL, 4: AND, 5: ORR, 6: LSLV, 7: LSRV, 8: EOR}[op], R(rd), na, nb))
    elif k in ('slli', 'srli'):
        _, rd, rs, sh = j
        if rd != 0:
            assert rd != SP
            n = src(rs, S1, out)
            out += [movz(S0, sh), rr(LSLV if k == 'slli' else LSRV, R(rd), n, S0)]
    elif k in ('beq', 'bne', 'bltu', 'bgeu'):
        _, a, bb, o = j
        na, nb = src(a, S0, out), src(bb, S1, out)
        out.append(cmp(na, nb))
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
