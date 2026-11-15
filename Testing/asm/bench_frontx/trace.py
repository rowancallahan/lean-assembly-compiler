#!/usr/bin/env python3
"""trace.py FN [ours|c]: tiny RV64I interpreter; per-pc execution counts of one call, difference between n=200 and n=100
(= the steady-state loop per byte).  Code: frontx-words/FN.words (ours) or c_FN from bench.c compiled -O2 (c)."""
import sys, os, subprocess, re, collections
D = os.path.dirname(os.path.abspath(__file__)); A = os.path.dirname(D)
src = open(os.path.join(D, "bench_frontx.py")).read().rsplit("mode, names", 1)[0]; exec(src)
fn = sys.argv[1]; kind = sys.argv[2] if len(sys.argv) > 2 else "ours"
if kind == "ours": code = [int(l, 16) for l in open(os.path.join(A, "frontx-words", fn + ".words")).read().split()[1:]]; base = 0
else:
    sh(f"riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -O2 -ffreestanding -nostdlib -fno-tree-loop-distribute-patterns -c {D}/bench.c -o {p('t.o')} && riscv64-linux-gnu-objcopy -O binary -j .text {p('t.o')} {p('t.bin')}")
    raw = open(p("t.bin"), "rb").read(); code = [int.from_bytes(raw[i:i+4], "little") for i in range(0, len(raw), 4)]
    base = int(re.search(rf"(\w+) T c_{fn}\n", sh(f"riscv64-linux-gnu-nm {p('t.o')}")).group(1), 16)
S = lambda x, b: x - (1 << b) if x >> (b - 1) else x
def run(n):
    xs = gen(n, FN[fn][0]); mem = bytearray(1 << 20); mem[0x10000:0x10000 + n] = xs
    r = [0] * 32; r[10], r[11], r[12], r[13], r[2] = 0x10000, n, 0x80000, 0x40000, 0xF0000
    if kind == "c": r[12] = 0x40000
    r[1] = 0xFFFFFFF0; pc = base; cnt = collections.Counter(); M = (1 << 64) - 1
    def ld(a, k, sg): v = int.from_bytes(mem[a:a + k], "little"); return S(v, 8 * k) & M if sg else v
    while pc != 0xFFFFFFF0:
        w = code[pc // 4]; cnt[pc] += 1; op = w & 127; rd = w >> 7 & 31; f3 = w >> 12 & 7; a = r[w >> 15 & 31]; b = r[w >> 20 & 31]; f7 = w >> 25; nx = pc + 4
        iI = S(w >> 20, 12); res = None
        if op == 0x37: res = S(w & 0xFFFFF000, 32) & M
        elif op == 0x17: res = (pc + S(w & 0xFFFFF000, 32)) & M
        elif op == 0x6F: res = nx; nx = pc + S(((w >> 31) << 20) | (w >> 12 & 255) << 12 | (w >> 20 & 1) << 11 | (w >> 21 & 1023) << 1, 21)
        elif op == 0x67: res = nx; nx = (a + iI) & ~1
        elif op == 0x63:
            im = S((w >> 31) << 12 | (w >> 7 & 1) << 11 | (w >> 25 & 63) << 5 | (w >> 8 & 15) << 1, 13)
            t = [a == b, a != b, 0, 0, S(a, 64) < S(b, 64), S(a, 64) >= S(b, 64), a < b, a >= b][f3]
            if t: nx = pc + im
        elif op == 0x03: res = ld((a + iI) & M, [1, 2, 4, 8, 1, 2, 4][f3], f3 < 4)
        elif op == 0x23:
            im = S((f7 << 5) | rd, 12); k = [1, 2, 4, 8][f3]; mem[(a + im) & M:(a + im + k) & M] = (b & ((1 << 8 * k) - 1)).to_bytes(k, "little")
        elif op in (0x13, 0x33):
            y = iI if op == 0x13 else b; sh_ = y & 63
            if op == 0x13 and f3 == 5: y = w >> 20 & 63; sh_ = y
            res = {0: lambda: a + y if op == 0x13 or f7 == 0 else a - y, 1: lambda: a << sh_, 2: lambda: int(S(a, 64) < S(y & M, 64)), 3: lambda: int(a < (y & M)),
                   4: lambda: a ^ y, 5: lambda: S(a, 64) >> sh_ if (w >> 30 & 1) else a >> sh_, 6: lambda: a | y, 7: lambda: a & y}[f3]() & M
        elif op in (0x1B, 0x3B):
            y = iI if op == 0x1B else b; sh_ = (w >> 20 & 31) if op == 0x1B else b & 31
            a32, y32 = a & 0xFFFFFFFF, y & 0xFFFFFFFF
            v = {0: lambda: a32 + y32 if op == 0x1B or f7 == 0 else a32 - y32, 1: lambda: a32 << sh_, 5: lambda: (S(a32, 32) >> sh_) if (w >> 30 & 1) else a32 >> sh_}[f3]()
            res = S(v & 0xFFFFFFFF, 32) & M
        else: raise Exception(f"op {w:08x} at {pc:x}")
        if res is not None and rd: r[rd] = res & M
        pc = nx
    return cnt
a, b = run(100), run(200); dis = {}
for l in sh(f"riscv64-linux-gnu-objdump -D -b binary -m riscv:rv64 {p('t.bin') if kind == 'c' else p('x.bin')}").splitlines() if kind == "c" else []: pass
tot = 0
words_dis = {}
open(p("x.bin"), "wb").write(b"".join(w.to_bytes(4, "little") for w in code))
for l in sh(f"riscv64-linux-gnu-objdump -D -b binary -m riscv:rv64 {p('x.bin')}").splitlines():
    m = re.match(r"\s+([0-9a-f]+):\t\S+\s+\t?(.*)", l)
    if m: words_dis[int(m.group(1), 16)] = m.group(2)
for pc in sorted(b):
    d = (b[pc] - a[pc]) / 100
    if d: tot += d; print(f"{pc:4x} x{d:<6g} {words_dis.get(pc, '?')}")
print("per byte:", tot, " fixed part (n=100):", sum(a.values()) - 100 * tot)
