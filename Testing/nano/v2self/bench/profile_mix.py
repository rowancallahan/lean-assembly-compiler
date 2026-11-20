#!/usr/bin/env python3
"""Dynamic instruction mix by opcode and by codegen pattern (static pattern labels x NANORUN_PROF per-word counts).
usage: mix.py CODE.bin PROF.bin"""
import struct, sys
from collections import Counter
raw = open(sys.argv[1], "rb").read()
W = struct.unpack("<%dI" % (len(raw) // 4), raw)
P = struct.unpack("<%dQ" % len(W), open(sys.argv[2], "rb").read())
N = len(W); T = sum(P)
def sx(v, b): return v - (1 << b) if v >> (b - 1) else v
def dec(x):
    op, rd, f3, a, b, f7 = x & 127, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31, (x >> 20) & 31, x >> 25
    I = sx(x >> 20, 12)
    if op == 0x13: return (["addi", "slli", "slti", "sltiu", "xori", "srli", "ori", "andi"][f3], rd, a, 0, I & 63 if f3 in (1, 5) else I)
    if op == 0x03: return ({3: "ld", 4: "lbu"}.get(f3, "load"), rd, a, 0, I)
    if op == 0x23: return ({3: "sd", 0: "sb"}.get(f3, "store"), 0, a, b, sx((f7 << 5) | rd, 12))
    if op == 0x63:
        imm = sx(((x >> 31) << 12) | (((x >> 7) & 1) << 11) | (((x >> 25) & 63) << 5) | (((x >> 8) & 15) << 1), 13)
        return ({0: "beq", 1: "bne", 6: "bltu", 7: "bgeu"}.get(f3, "br"), 0, a, b, imm)
    if op == 0x6f:
        imm = sx(((x >> 31) << 20) | (((x >> 12) & 255) << 12) | (((x >> 20) & 1) << 11) | (((x >> 21) & 1023) << 1), 21)
        return ("jal", rd, 0, 0, imm)
    if op == 0x67: return ("jalr", rd, a, 0, I)
    if op == 0x33:
        n = {(0, 0): "add", (32, 0): "sub", (1, 0): "mul", (0, 7): "and", (0, 6): "or", (0, 1): "sll", (0, 5): "srl", (0, 4): "xor"}[(f7, f3)]
        return (n, rd, a, b, 0)
    return ("?", 0, 0, 0, 0)
D = [dec(x) for x in W]
assert all(d[0] != "?" or P[i] == 0 for i, d in enumerate(D)), "undecoded executed word"
lab = [None] * N
def m(i, pat):
    """pat: list of predicates/tuples; None fields are wildcards"""
    if i + len(pat) > N: return False
    for k, p in enumerate(pat):
        d = D[i + k]
        if callable(p):
            if not p(d): return False
        elif any(q is not None and q != e for q, e in zip(p, d)): return False
    return True
def mark(i, n, name):
    for k in range(n):
        assert lab[i + k] is None, (i, k, name, lab[i + k]); lab[i + k] = name
PUSH = lambda r=None: [("addi", 31, 31, 0, -8), ("bgeu", 0, 31, 30, 8), ("jal", 0, 0, 0, None), ("sd", 0, 31, r, 0)]
entries = sorted({i + D[i][4] // 4 for i in range(N) if D[i][0] == "jal" and D[i][1] == 1})
ends = {e: (entries[k + 1] if k + 1 < len(entries) else N) for k, e in enumerate(entries)}
PRO = PUSH(1) + PUSH(8) + [("addi", 8, 31, 0, 0), ("addi", 31, 31, 0, None), ("bgeu", 0, 31, 30, 8), ("jal", 0, 0, 0, None)]
for e in entries:
    assert m(e, PRO), e
    mark(e, 12, "prologue")
LIBIG = [("addi", None, 0, 0, 0)] + [("slli", None, None, 0, 8), ("addi", None, None, 0, None)] * 8
libig = {}
i = 0
while i < N:
    if lab[i]: i += 1; continue
    if m(i, [("ld", 14, 8, 0, 8), ("ld", 15, 8, 0, 0)]):
        j = i + 2
        while m(j, [("ld", 5, 31, 0, None), ("sd", 0, 8, 5, None)]): j += 2
        assert m(j, [("addi", 31, 8, 0, None), ("addi", 8, 15, 0, 0), ("jalr", 0, 14, 0, 0)]), j
        mark(i, j + 3 - i, "epilogue"); i = j + 3; continue
    if m(i, LIBIG) and len({D[i + k][1] for k in range(17)}) == 1:
        v = 0
        for k in range(8): v = (v << 8) + D[i + 2 + 2 * k][4]
        libig[i] = v; mark(i, 17, "li_big"); i += 17; continue
    if m(i, PUSH()): mark(i, 4, "push"); i += 4; continue
    if m(i, [("ld", 6, 31, 0, 0), ("ld", 5, 31, 0, 8), ("addi", 31, 31, 0, None)]) and D[i + 2][4] in (8, 16):
        if D[i + 2][4] == 8 and m(i + 3, [(None, 5, 5, 6, 0), ("sd", 0, 31, 5, 0)]) and D[i + 3][0] in ("add", "sub", "mul", "and", "or", "sll", "srl", "xor"):
            mark(i, 5, "binop"); i += 5; continue
        if D[i + 2][4] == 16 and m(i + 3, [(None, 0, 5, 6, 8), ("jal", 0, 0, 0, None)]) and D[i + 3][0] in ("beq", "bltu"):
            mark(i, 4, "if_cmp"); lab[i + 4] = "if_jal_else"; i += 5; continue
        if D[i + 2][4] == 8 and m(i + 3, [("ld", 7, 5, 0, 0), ("addi", 14, 0, 0, 0), ("bgeu", 0, 6, 7, 16)]):
            mark(i, 10, "bget"); i += 10; continue
        if D[i + 2][4] == 8 and m(i + 3, [("ld", 7, 5, 0, 0), ("ld", 14, 5, 0, 8), ("bltu", 0, 7, 14, 8)]):
            mark(i, 12, "bpush"); i += 12; continue
        assert 0, ("pop2?", i, D[i:i + 8])
    if m(i, [("ld", 14, 31, 0, 0), ("ld", 6, 31, 0, 8), ("ld", 5, 31, 0, 16), ("addi", 31, 31, 0, 16)]):
        mark(i, 9, "bset"); i += 9; continue
    if m(i, [("ld", 5, 31, 0, 0), ("ld", 5, 5, 0, 0), ("sd", 0, 31, 5, 0)]): mark(i, 3, "bsize"); i += 3; continue
    if m(i, [("ld", 6, 31, 0, 0), ("addi", 5, 0, 0, 0), ("bgeu", 0, 6, 29, 12)]): mark(i, 6, "rd"); i += 6; continue
    if m(i, [("ld", 5, 31, 0, 0), ("addi", 31, 31, 0, 8), ("sd", 0, 8, 5, None)]): mark(i, 3, "pop_to_slot"); i += 3; continue
    if m(i, [("ld", 5, 8, 0, None), ("beq", 0, 5, 0, 8), ("jal", 0, 0, 0, None)]):
        mark(i, 2, "loop_head"); lab[i + 2] = "loop_jal_step"; i += 3; continue
    if m(i, [("addi", 5, 5, 0, -1), ("sd", 0, 8, 5, None)]): mark(i, 2, "loop_fuel_dec"); i += 2; continue
    if m(i, [("ld", 5, 8, 0, None)]): lab[i] = "local_ld"; i += 1; continue
    if m(i, [("addi", 5, 0, 0, None)]): lab[i] = "li_small"; i += 1; continue
    if D[i][0] == "jal" and D[i][1] == 1: lab[i] = "call_jal"; i += 1; continue
    if D[i][0] == "jal" and D[i][1] == 0: lab[i] = "jal_other(then-end/continue/exit)"; i += 1; continue
    lab[i] = "other(start/stubs/bnew)"; i += 1
C4OUT = []
pct0 = lambda v: f"{100 * v / T:6.2f}%"
import bisect
def fn(i):
    return entries[bisect.bisect_right(entries, i) - 1] if i >= entries[0] else None
# const defs
body = {e: list(range(e + 12, ends[e])) for e in entries}
def shape(e):
    return [lab[i] for i in body[e]]
lit = {}
for e in entries:
    s = shape(e); n = len(s)
    if D[e + 9][4] != 0: continue
    if n == 1 + 4 + 7 and s[0] == "li_small" and s[-1] == "epilogue" and s[1] == "push": lit[e] = D[e + 12][4]
    if n == 17 + 4 + 7 and s[0] == "li_big" and s[-1] == "epilogue": lit[e] = libig[e + 12]
const = set(lit)
ch = True
while ch:
    ch = False
    for e in entries:
        if e in const or D[e + 9][4] != 0: continue
        ok = True
        for i in body[e]:
            if lab[i] in ("li_small", "li_big", "push", "binop", "epilogue"): continue
            if lab[i] == "call_jal" and i + D[i][4] // 4 in const: continue
            ok = False; break
        # zero args: epilogue stores result at 8(x8)
        if ok and D[ends[e] - 4] == ("sd", 0, 8, 5, 8): const.add(e); ch = True
lit_calls = sum(P[e] for e in lit)
c4a = 17 * lit_calls
inner = sum(P[i] for e in const for i in range(e, ends[e]))
ext_calls = sum(P[i] for i in range(N) if lab[i] == "call_jal" and i + D[i][4] // 4 in const and fn(i) not in const)
int_calls = sum(P[i] for i in range(N) if lab[i] == "call_jal" and i + D[i][4] // 4 in const and fn(i) in const)
ext_big = sum(P[i] for i in range(N) if lab[i] == "call_jal" and i + D[i][4] // 4 in const and fn(i) not in const and (i + D[i][4] // 4 not in lit or lit[i + D[i][4] // 4] >= 2048))
c4b_cur = inner + ext_calls - (ext_calls - ext_big) * 4 - ext_big * 20
c4b_good = inner + ext_calls - (ext_calls - ext_big) * 4 - ext_big * 5
C4OUT.append(f"C4a inline literal defs only: {len(lit)} defs, {lit_calls} calls x17 = {c4a} {pct0(c4a)}")
C4OUT.append(f"C4b fold all constant defs ({len(const)} defs; executed inside {inner} {pct0(inner)}; calls from non-const code {ext_calls}, of which value>=2048: {ext_big}; const->const calls {int_calls})")
C4OUT.append(f"     saved with current 17-word li: {c4b_cur} {pct0(c4b_cur)}; with a 2-word li: {c4b_good} {pct0(c4b_good)}")

MODE = sys.argv[3] if len(sys.argv) > 3 else "all"
T0 = T
if MODE == "noconst":   # the profile AFTER folding constant defs (C4b) with a 2-word li for >= 2048
    P = list(P)
    ext = [(i, i + D[i][4] // 4) for i in range(N) if lab[i] == "call_jal" and i + D[i][4] // 4 in const and fn(i) not in const]
    FOLD = sum(P[i] * (4 if (t in lit and lit[t] < 2048) else 5) for i, t in ext)   # li + push (3 executed)
    FOLDPUSH = sum(P[i] for i, t in ext)
    for i, t in ext: P[i] = 0
    for e in const:
        for i in range(e, ends[e]): P[i] = 0
    T = sum(P) + FOLD
    print(f"MODE noconst: constant defs folded at their {len(ext)} call sites: total {T0} -> {T} ({100*T/T0:.2f}%)")
else: FOLD = FOLDPUSH = 0
# ---- tables
ops = Counter(); pats = Counter(); stat = Counter()
for i in range(N):
    ops[D[i][0]] += P[i]; pats[lab[i]] += P[i]; stat[lab[i]] += 1
pct = lambda v: f"{100 * v / T:6.2f}%"
print(f"total executed {T}; code words {N}; functions {len(entries)}")
print("-- by opcode"); [print(f"  {k:8s} {v:13d} {pct(v)}") for k, v in ops.most_common() if v]
print("-- by pattern (static words | executed | share)"); [print(f"  {k:36s} {stat[k]:6d} {v:13d} {pct(v)}") for k, v in pats.most_common()]
# ---- candidate savings
E = lambda i: P[i]
push_at = [i for i in range(N) if lab[i] == "push" and D[i] == ("addi", 31, 31, 0, -8) and (i == 0 or lab[i - 1] != "push" or D[i - 1][0] == "sd")]
push_at = [i for i in push_at if m(i, PUSH())]
calls = sum(P[e] for e in entries)
c1 = sum(P[i + 1] for i in push_at) + sum(P[e + 1] + P[e + 5] for e in entries) + sum(P[e + 9] for e in entries if D[e + 9][4] == 0) - calls
print("\n-- candidate savings (executed instructions removed)")
print(f"C1 one check/function: push bgeu's {sum(P[i+1] for i in push_at)+sum(P[e+1]+P[e+5] for e in entries)} + zero-frame addi {sum(P[e+9] for e in entries if D[e+9][4]==0)} - 1/call {calls} = {c1} {pct(c1)}")
IMMOK = ("add", "sub", "and", "or", "sll", "srl", "xor")
def right_leaf(kind):
    b = c = bm = 0
    for i in push_at:
        if lab[i - 1] != kind: continue
        j = i + 4
        if lab[j] == "binop" and D[j] == ("ld", 6, 31, 0, 0):
            if D[j + 3][0] in IMMOK or kind == "local_ld": b += P[j]
            else: bm += P[j]
        if lab[j] == "if_cmp" and D[j] == ("ld", 6, 31, 0, 0): c += P[j]
    return b, c, bm
b, c, bm = right_leaf("li_small")
print(f"C2 small-imm right operand: BIN {b} execs x6 + compare {c} execs x4 = {6*b+4*c} {pct(6*b+4*c)}   (after C1: {5*b+3*c} {pct(5*b+3*c)}); mul-by-const execs {bm} not covered")
bl, cl, _ = right_leaf("local_ld")
print(f"C2' leaf-LOCAL right operand: BIN {bl} x5 + compare {cl} x4 = {5*bl+4*cl} {pct(5*bl+4*cl)}  (after C1: {4*bl+3*cl} {pct(4*bl+3*cl)})")
allbin = sum(P[i] for i in range(N) if lab[i] == "binop" and D[i] == ("ld", 6, 31, 0, 0))
allcmp = sum(P[i] for i in range(N) if lab[i] == "if_cmp" and D[i] == ("ld", 6, 31, 0, 0))
print(f"   (all BIN execs {allbin}, all compare execs {allcmp})")
c3 = pats["if_jal_else"] + pats["loop_jal_step"]
print(f"C3 direct cond branch: if-else jal {pats['if_jal_else']} + loop-step jal {pats['loop_jal_step']} = {c3} {pct(c3)}")
print('\n'.join(C4OUT))
lb = sum(P[i] for i in libig); big31 = sum(P[i] for i, v in libig.items() if v < 2**31 - 2048)
print(f"C6 short li: li_big execs {lb} (value < 2^31: {big31}) x15 = {15*big31} {pct(15*big31)};  distinct values {sorted(set(libig.values()))[:40]}")
# push followed by pop of top
adj5 = sum(P[i] for i in push_at if D[i + 4] == ("ld", 5, 31, 0, 0))
adj6 = sum(P[i] for i in push_at if D[i + 4] == ("ld", 6, 31, 0, 0))
slot = sum(P[i] for i in push_at if lab[i + 4] == "pop_to_slot")
epi = sum(P[i] for i in push_at if lab[i + 4] == "epilogue")
pushes = sum(P[i] for i in push_at)
print(f"C5 TOS register: pushes {pushes}; push->pop-top adjacency: into t1 {adj6}, into t0 {adj5} (pop_to_slot {slot}); push then epilogue {epi}")
print(f"     always-TOS-in-t0 model: -2 per BIN = {2*allbin} {pct(2*allbin)}; cached-flag model (sd+ld of each adjacent pair, addi folded): {2*(adj5+adj6)+epi*2} {pct(2*(adj5+adj6)+2*epi)} .. {4*(adj5+adj6)} {pct(4*(adj5+adj6))}")
print(f"X1 push;pop_to_slot peephole (LET of a just-computed value): {slot} x5 = {5*slot} {pct(5*slot)} (after C1: x4 {pct(4*slot)})")
print(f"X2 calls {calls}: prologue {pats['prologue']} {pct(pats['prologue'])}, epilogue {pats['epilogue']} {pct(pats['epilogue'])}, call jal {pats['call_jal']}")
# ---- extra patterns
calls_nc = sum(P[e] for e in entries)
recheck = c1 - 2 * calls_nc      # C1 with a 2-instruction re-check after every call return (the callee may have raised t5)
print(f"C1' one check/function + re-check after each call: {recheck} {pct(recheck)}")
cont = sum(P[i] for i in range(N) if lab[i] == "jal_other(then-end/continue/exit)")
print(f"X3 fuel per loop iteration: head ld+beq+jal + dec addi+sd = 5; iterations {pats['loop_jal_step']}")
print(f"X4 bget {pats['bget']} {pct(pats['bget'])} (10/exec), bset {pats['bset']} {pct(pats['bset'])}, bpush {pats['bpush']} {pct(pats['bpush'])}")
argpush = sum(P[i] for i in push_at if lab[i - 1] == "local_ld")
print(f"X5 LOCAL pushes {argpush}; li_small pushes {sum(P[i] for i in push_at if lab[i-1]=='li_small')}; li_big pushes {sum(P[i] for i in push_at if lab[i-1]=='li_big')}; other pushes(results) {pushes - argpush - sum(P[i] for i in push_at if lab[i-1] in ('li_small','li_big'))}")
zero_cmp = sum(P[i] for i in push_at if lab[i - 1] == "li_small" and D[i - 1][4] == 0 and lab[i + 4] == "if_cmp")
print(f"X6 compare with literal 0: {zero_cmp}")
# call overhead for non-literal functions: per call jal 1 + prologue 9 + epilogue 5+2*nres
print(f"X7 call overhead: calls {calls_nc}, prologue+epilogue+jal = {pats['prologue']+pats['epilogue']+pats['call_jal']} {pct(pats['prologue']+pats['epilogue']+pats['call_jal'])}")
import json
print("JSON " + json.dumps(dict(total=T, total0=T0, c1=c1, c1r=recheck, c2=6*b+4*c, c2_after_c1=5*b+3*c, c2l=5*bl+4*cl, c2l_after_c1=4*bl+3*cl, c3=c3,
    c4a=c4a, c4b=c4b_good, c4b_curli=c4b_cur, c6=15*big31, tos_lo=2*allbin, tos_hi=2*(adj5+adj6)+2*epi, x1=5*slot, push=pats["push"], pro=pats["prologue"], epi=pats["epilogue"],
    libig=pats["li_big"], bget=pats["bget"], calls=calls_nc, ops={k: v for k, v in ops.items() if v})))
def nb(v):
    k = 1
    while v >> (8 * k): k += 1
    return k
if MODE == "all":
    li_sv = sum(P[i] * (17 - (2 * nb(v) - 1)) for i, v in libig.items())
    print(f"D-byte li (skip leading zero bytes, addi/slli only): saves {li_sv} {pct(li_sv)}")
    # source flattening: every constant def becomes a literal def (call 1 + prologue 9 + li + push 3 + epilogue 7)
    val = {}
    cost_now = cost_flat = cost_flat_li = 0
    for i in range(N):
        if lab[i] == "call_jal" and i + D[i][4] // 4 in const and fn(i) not in const:
            t = i + D[i][4] // 4
            cost_flat += P[i] * 37; cost_flat_li += P[i] * 37   # upper bound: assume every folded value is big (17-word li)
    small = ext_calls - ext_big
    flat = inner + ext_calls - (small * 21 + ext_big * 37)
    flat_li = inner + ext_calls - (small * 21 + ext_big * 25)   # with a 5-word li (3-byte values)
    print(f"SRC flatten chained constant defs to literals (no compiler change): saves {flat} {pct(flat)}; plus byte li: {flat_li} {pct(flat_li)}")
    nonconst_li = sum(P[i] * (17 - (2 * nb(v) - 1)) for i, v in libig.items() if fn(i) not in const)
    print(f"   byte-li saving outside constant defs: {nonconst_li} {pct(nonconst_li)}")
