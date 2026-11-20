"""Random RV64 word streams for the rv2arm fuzzer. Standard RV64 encodings; J subset only (addi, slli, srli, ld, sd,
lbu, sb, add/sub/mul/and/or/sll/srl/xor, beq/bne/bltu/bgeu, jal, jalr x0). Immediates are 12-bit (-2048..2047)."""
import random

DEST = [0, 1, 2, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 28, 29, 30, 31]  # mapped RV regs (x0 = no-op dest; x2 = sp -> A64 x4)
SRC = DEST
NZ = [r for r in SRC if r]
ALU = [(0, 0), (0, 32), (0, 1), (7, 0), (6, 0), (1, 0), (5, 0), (4, 0)]
BR = [0, 1, 6, 7]
B12 = [-2048, -2047, -257, -256, -255, -9, -8, -1, 0, 1, 3, 7, 8, 255, 256, 2046, 2047]

def I(op, f3, rd, rs, imm): return op | rd << 7 | f3 << 12 | rs << 15 | (imm & 0xFFF) << 20
def S(op, f3, rs1, rs2, imm): return op | (imm & 31) << 7 | f3 << 12 | rs1 << 15 | rs2 << 20 | ((imm >> 5) & 127) << 25
def R(f3, f7, rd, rs1, rs2): return 0x33 | rd << 7 | f3 << 12 | rs1 << 15 | rs2 << 20 | f7 << 25
def B(f3, rs1, rs2, off):
    i = off & 0x1FFF
    return 0x63 | (i >> 11 & 1) << 7 | (i >> 1 & 15) << 8 | f3 << 12 | rs1 << 15 | rs2 << 20 | (i >> 5 & 63) << 25 | (i >> 12 & 1) << 31
def J(rd, off):
    i = off & 0x1FFFFF
    return 0x6F | rd << 7 | (i >> 12 & 255) << 12 | (i >> 11 & 1) << 20 | (i >> 1 & 1023) << 21 | (i >> 20 & 1) << 31

def valid_word(rng, i, n, straight=False):
    """One valid J word at index i of an n-word program. straight: no branches/jumps; ld/sd only off x5/x2 and 8-aligned."""
    k = rng.random()
    D = [r for r in DEST if r != 5] if straight else DEST      # straight: x5 is the memory base, never written
    if k < 0.12:
        return I(0x13, 0, rng.choice(D), rng.choice(SRC), rng.choice(B12) if rng.random() < .6 else rng.randint(-2048, 2047))
    if k < 0.16:
        return I(0x13, rng.choice([1, 5]), rng.choice(D), rng.choice(SRC), rng.randint(0, 63))
    if k < 0.36:
        if straight:
            base = 5; off = rng.choice([-2048, -256, -8, 0, 8, 256, 2040]) if rng.random() < .5 else rng.randrange(-256, 256, 8)
            return I(0x03, 3, rng.choice(D), base, off) if rng.random() < .5 else S(0x23, 3, base, rng.choice(D), off)
        base = rng.choice(NZ); off = rng.choice(B12) if rng.random() < .5 else rng.randint(-2048, 2047)
        if rng.random() < .5: return I(0x03, 3, rng.choice(D), base, off)
        return S(0x23, 3, base, rng.choice(D), off)
    if k < 0.46:
        if straight:
            base = 5; off = rng.choice(B12) if rng.random() < .5 else rng.randint(-2048, 2047)
        else:
            base = rng.choice(NZ); off = rng.choice(B12) if rng.random() < .5 else rng.randint(-2048, 2047)
        if rng.random() < .5: return I(0x03, 4, rng.choice(D), base, off)
        return S(0x23, 0, base, rng.choice(D), off)
    if k < 0.70:
        f3, f7 = rng.choice(ALU)
        return R(f3, f7, rng.choice(D), rng.choice(SRC), rng.choice(SRC))
    if straight:
        return I(0x13, 0, rng.choice(D), rng.choice(SRC), 1)
    if k < 0.85:
        t = rng.randrange(max(0, i - 1024), min(n, i + 1024)) if n > 1 else 0
        return B(rng.choice(BR), rng.choice(SRC), rng.choice(SRC), 4 * (t - i))
    if k < 0.93:
        t = rng.randrange(n)
        return J(rng.choice([0, 1]), 4 * (t - i))
    return I(0x67, 0, 0, rng.choice(NZ), 0)                                   # jalr x0, 0(rs)

INVALID = [
    lambda r: 0x00000073, lambda r: 0x00100073,                              # ecall, ebreak
    lambda r: I(0x13, 2, r.choice(DEST), r.choice(SRC), r.choice(B12)),      # slti
    lambda r: I(0x13, 4, r.choice(DEST), r.choice(SRC), r.choice(B12)),      # xori
    lambda r: I(0x13, 6, r.choice(DEST), r.choice(SRC), r.choice(B12)),      # ori
    lambda r: I(0x13, 7, r.choice(DEST), r.choice(SRC), r.choice(B12)),      # andi
    lambda r: I(0x13, 5, r.choice(DEST), r.choice(SRC), 1 << 10 | r.randint(0, 63)),   # srai (bit 30)
    lambda r: I(0x1B, 0, r.choice(DEST), r.choice(SRC), r.choice(B12)),      # addiw
    lambda r: R(5, 32, r.choice(DEST), r.choice(SRC), r.choice(SRC)),        # sra
    lambda r: R(1, 1, r.choice(DEST), r.choice(SRC), r.choice(SRC)),         # mulh
    lambda r: R(4, 1, r.choice(DEST), r.choice(SRC), r.choice(SRC)),         # div
    lambda r: R(2, 0, r.choice(DEST), r.choice(SRC), r.choice(SRC)),         # slt
    lambda r: R(0, 2, r.choice(DEST), r.choice(SRC), r.choice(SRC)),         # f7=2
    lambda r: I(0x03, 0, r.choice(DEST), r.choice(NZ), r.choice(B12)),       # lb
    lambda r: I(0x03, 2, r.choice(DEST), r.choice(NZ), r.choice(B12)),       # lw
    lambda r: I(0x03, 3, r.choice(DEST), 0, r.choice(B12)),                  # ld x?, off(x0)
    lambda r: S(0x23, 1, r.choice(NZ), r.choice(DEST), r.choice(B12)),       # sh
    lambda r: S(0x23, 2, r.choice(NZ), r.choice(DEST), r.choice(B12)),       # sw
    lambda r: I(0x13, 0, 3, r.choice(SRC), r.choice(B12)),                   # unmapped dest x3
    lambda r: I(0x13, 0, r.choice(DEST), 4, r.choice(B12)),                  # unmapped src x4
    lambda r: R(0, 0, r.choice(DEST), 16, r.choice(SRC)),                    # unmapped x16
    lambda r: B(2, 1, 2, 8), lambda r: B(3, 1, 2, 8),                        # beq/bne funct3 2, 3
    lambda r: B(0, 1, 2, 2),                                                 # branch offset 2 (not %4)
    lambda r: B(0, 1, 2, 4 * 5000),                                          # branch out of range
    lambda r: J(2, 8), lambda r: J(1, 2),                                    # jal sp / misaligned
    lambda r: I(0x67, 0, 1, r.choice(NZ), 0),                                # jalr ra, 0(rs)
    lambda r: I(0x67, 0, 0, r.choice(NZ), 4),                                # jalr with offset 4
    lambda r: 0x00000037 | r.choice(DEST) << 7, lambda r: 0x00000017 | r.choice(DEST) << 7,  # lui, auipc
    lambda r: I(0x13, 0, 0, r.choice([3, 4, 9, 16]), r.choice(B12)),         # rd=x0, unmapped source (oracle emits; nano refuses)
    lambda r: 0x00000067,                                                    # jalr x0, 0(x0) (same split)
    lambda r: r.getrandbits(32),                                             # random word
]

def mutate(rng, prog):
    """Replace or bit-flip one word: near-miss encodings and random words."""
    p = list(prog); i = rng.randrange(len(p)); n = len(p)
    if rng.random() < 0.5:
        p[i] = rng.choice(INVALID)(rng)
    else:
        p[i] ^= 1 << rng.randrange(32)
    return p

def program(rng, n, straight=False):
    return [valid_word(rng, i, n, straight) for i in range(n)]

def words_to_bytes(ws):
    return b''.join((w & 0xFFFFFFFF).to_bytes(4, 'little') for w in ws)

def case(rng, kind, n=None):
    """Returns (label, bytes)."""
    if kind == 'valid':
        n = n or rng.choice([1, 2, 3, 5, 8, 16, 30, 60, 200])
        return 'valid', words_to_bytes(program(rng, n))
    if kind == 'mutant':
        p = program(rng, n or rng.choice([2, 5, 12, 40]))
        return 'mutant', words_to_bytes(mutate(rng, p))
    if kind == 'random':
        return 'random', words_to_bytes([rng.getrandbits(32) for _ in range(n or rng.choice([1, 2, 4, 9]))])
    if kind == 'invalid1':
        p = program(rng, rng.choice([1, 4, 9])); j = rng.randrange(len(p))
        p[j] = rng.choice(INVALID)(rng)
        return 'invalid1', words_to_bytes(p)
    if kind == 'odd':
        p = program(rng, rng.choice([1, 7])); b = words_to_bytes(p)
        return 'odd', b[:-rng.randint(1, 3)] if rng.random() < .5 else b + bytes(rng.randint(1, 3))
    if kind == 'empty':
        return 'empty', b''
    if kind == 'chunk':
        return 'chunk', words_to_bytes(program(rng, n))
    raise ValueError(kind)
