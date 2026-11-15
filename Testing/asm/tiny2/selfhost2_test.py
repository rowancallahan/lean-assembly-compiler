#!/usr/bin/env python3
"""usage: selfhost2_test.py sN. (a) the front-end binary of step N's compiler (`frontx-words/tiny2_sN.words`) runs on
qemu-system-riscv64 on every source in `tiny2_sN.cases`; its output must equal Lean's (the same bytes as
`frontx_test.py check`), and (b) its output, executed (step 1-4: Python stack machine on the instruction bytes; step 5:
RV64 words on qemu-riscv64 via driver2.c), must give Lean's value of the source (`sN.run`: source hex, x, value)."""
import os, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "work"); os.makedirs(W, exist_ok=True)
STEP = sys.argv[1]
sys.argv = ["frontx_test.py", "-", "0", "tiny2_" + STEP]
sys.path.insert(0, os.path.dirname(D))
import frontx_test as F
M = (1 << 64) - 1
def decode(b):  # Ins bytes: 0 nil | 1 push n | 2 ldx | 3 op k   (prefix, scalar 8 bytes LE before the child)
    out, i = [], 0
    while True:
        t = b[i]; i += 1
        if t == 0: return out
        if t in (1, 3): out.append((t, int.from_bytes(b[i:i + 8], "little"))); i += 8
        else: out.append((t, 0))
def apply(k, a, b): return (a + b) & M if k == 0 else (a - b) & M if k == 1 else a ^ b
def run_stack(code, x):
    s = []
    for t, n in code:
        if t == 1: s.append(n)
        elif t == 2: s.append(x)
        else: b = s.pop(); a = s.pop(); s.append(apply(n, a, b))
    return s[-1] if s else 0
def apply2(k, a, b):
    return (a + b) & M if k == 0 else (a - b) & M if k == 1 else a ^ b if k == 2 else int(a < b) if k == 3 else int(a == b)
sys.setrecursionlimit(100000)
def parse(b):  # step 2 type T: 0 nil | 1 lit n | 2 var | 3 bin k a b | 4 op k rest  (prefix, scalar 8 bytes LE first)
    def go(i):
        t = b[i]; i += 1
        if t == 0: return ("nil",), i
        if t == 2: return ("var",), i
        n = int.from_bytes(b[i:i + 8], "little"); i += 8
        if t == 1: return ("lit", n), i
        a, i = go(i)
        if t == 4: return ("op", n, a), i
        c, i = go(i); return ("bin", n, a, c), i
    r, i = go(0); assert i == len(b); return r
def run_s2(code, x):
    s = []; node = parse(code)
    while node[0] != "nil":
        if node[0] == "bin":  # push imm (k = 9) or load x (k = 10)
            s.append(node[3][1] if node[1] == 9 else x); node = node[2]
        else:
            _, k, node = node
            if k < 5: b = s.pop(); a = s.pop(); s.append(apply2(k, a, b))
            elif k == 5: b = s.pop(); s.pop(); s.append(b)
            elif k == 6: x = s[-1]
            elif k == 7: c = s.pop(); e = s.pop(); t = s.pop(); s.append(t if c else e)
    return s[-1] if s else 0
run_code = (lambda code, x: run_stack(decode(code), x)) if STEP == "s1" else run_s2
cases = F.CASES
lay, halt, base, tab, size = F.build([(c[0], [0] * (len(c[1]) + 64), c[2]) for c in cases], "".join(f"  .word 0x{w:08x}\n" for w in F.words))
mem = F.qemu(halt, base, tab + F.E * len(cases) - base)
got = {}
for c, ((i0, o0, w0), case) in enumerate(zip(lay, cases)):
    a1 = int.from_bytes(mem[tab - base + F.E * c + 64:][:8], "little")
    out = bytes(mem[o0:o0 + a1]); assert out == bytes(case[1]), ("binary != Lean", bytes(case[0]).hex())
    got[bytes(case[0]).hex()] = out
n = 0
for l in open(os.path.join(D, STEP + ".run")):
    src, x, want = l.split(); out = got[src]
    assert run_code(out, int(x)) == int(want), (src, x, want)
    n += 1
print(f"{STEP}: {len(cases)} sources compiled by the binary on QEMU (== Lean); {n} runs of the output == Lean eval")
