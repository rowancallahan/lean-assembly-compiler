#!/usr/bin/env python3
"""trace_ind.py FN: RV64I interpreter over frontx-words/<FN>.words (an `ind` entry); per-pc counts of one call at two input sizes,
difference = the steady-state cost per node. Prints per-function share (functions = jal targets), mnemonic mix, hottest pcs."""
import sys, os, re, collections, subprocess, random
D = os.path.dirname(os.path.abspath(__file__)); A = os.path.dirname(D)
sys.argv = [sys.argv[0], "x"] + sys.argv[1:]
fn = sys.argv[2]; WN = {"count": "bt_count", "mirror": "bt_mirror", "nontail": "nontail_sum_ln", "reverse": "tail_reverse_ln", "append": "list_append_ln", "hasparam": "level_hasparam"}[fn]
src = open(os.path.join(D, "bench_ind.py")).read().split("def harness")[0]; exec(src)
ws = [l.strip() for l in open(os.path.join(A, "frontx-words", WN + ".words")) if l.strip()]; h = ws[0].split(); A0, B0 = int(h[1]), int(h[2])
code = [int(w, 16) for w in ws[1:]]
S = lambda x, b: x - (1 << b) if x >> (b - 1) else x
def run(inp):
    n = len(inp); wk = A0 + B0 * n; MEM = 0x20000 + wk + 0x10000; mem = bytearray(MEM); mem[0x1000:0x1000 + n] = inp
    r = [0] * 32; r[10], r[11], r[12], r[13], r[2] = 0x1000, n, 0x20000, 0x1000 + n + 64, 0x20000 + wk
    r[1] = 0xFFFFFFF0; pc = 0; cnt = collections.Counter(); Mk = (1 << 64) - 1; tg = collections.Counter()
    def ld(a, k, sg): v = int.from_bytes(mem[a:a + k], "little"); return S(v, 8 * k) & Mk if sg else v
    while pc != 0xFFFFFFF0:
        w = code[pc // 4]; cnt[pc] += 1; op = w & 127; rd = w >> 7 & 31; f3 = w >> 12 & 7; a = r[w >> 15 & 31]; b = r[w >> 20 & 31]; f7 = w >> 25; nx = pc + 4
        iI = S(w >> 20, 12); res = None
        if op == 0x37: res = S(w & 0xFFFFF000, 32) & Mk
        elif op == 0x17: res = (pc + S(w & 0xFFFFF000, 32)) & Mk
        elif op == 0x6F: res = nx; nx = pc + S(((w >> 31) << 20) | (w >> 12 & 255) << 12 | (w >> 20 & 1) << 11 | (w >> 21 & 1023) << 1, 21); tg[nx] += 1
        elif op == 0x67: res = nx; nx = (a + iI) & ~1
        elif op == 0x63:
            im = S((w >> 31) << 12 | (w >> 7 & 1) << 11 | (w >> 25 & 63) << 5 | (w >> 8 & 15) << 1, 13)
            t = [a == b, a != b, 0, 0, S(a, 64) < S(b, 64), S(a, 64) >= S(b, 64), a < b, a >= b][f3]
            if t: nx = pc + im
        elif op == 0x03: res = ld((a + iI) & Mk, [1, 2, 4, 8, 1, 2, 4][f3], f3 < 4)
        elif op == 0x23:
            im = S((f7 << 5) | rd, 12); k = [1, 2, 4, 8][f3]; mem[(a + im) & Mk:(a + im + k) & Mk] = (b & ((1 << 8 * k) - 1)).to_bytes(k, "little")
        elif op in (0x13, 0x33):
            y = iI if op == 0x13 else b; sh_ = y & 63
            if op == 0x13 and f3 == 5: y = w >> 20 & 63; sh_ = y
            res = {0: lambda: a + y if op == 0x13 or f7 == 0 else a - y, 1: lambda: a << sh_, 2: lambda: int(S(a, 64) < S(y & Mk, 64)), 3: lambda: int(a < (y & Mk)),
                   4: lambda: a ^ y, 5: lambda: S(a, 64) >> sh_ if (w >> 30 & 1) else a >> sh_, 6: lambda: a | y, 7: lambda: a & y}[f3]() & Mk
        elif op in (0x1B, 0x3B):
            y = iI if op == 0x1B else b; sh_ = (w >> 20 & 31) if op == 0x1B else b & 31
            a32, y32 = a & 0xFFFFFFFF, y & 0xFFFFFFFF
            v = {0: lambda: a32 + y32 if op == 0x1B or f7 == 0 else a32 - y32, 1: lambda: a32 << sh_, 5: lambda: (S(a32, 32) >> sh_) if (w >> 30 & 1) else a32 >> sh_}[f3]()
            res = S(v & 0xFFFFFFFF, 32) & Mk
        else: raise Exception(f"op {w:08x} at {pc:x}")
        if res is not None and rd: r[rd] = res & Mk
        pc = nx
    return cnt, tg, mem[0x1000 + n + 64: 0x1000 + n + 64 + 16]
rnd = random.Random(7); n1, n2 = (127, 511) if fn in ("count", "mirror") else (200, 800)
i1, e1, k1 = gen(fn, n1, rnd); i2, e2, k2 = gen(fn, n2, rnd)
(a, tga, o1), (b, tgb, o2) = run(i1), run(i2)
if fn != "hasparam": assert o2[:len(e2)] == e2[:16], (o2.hex(), e2[:16].hex())
dn = k2 - k1; d = {pc: (b[pc] - a[pc]) / dn for pc in b if b[pc] != a[pc]}
open(p("w.bin"), "wb").write(b"".join(w.to_bytes(4, "little") for w in code))
dis = {}
for l in sh(f"riscv64-linux-gnu-objdump -D -b binary -m riscv:rv64 {p('w.bin')}").splitlines():
    m = re.match(r"\s+([0-9a-f]+):\t\S+\s+\t?(.*)", l)
    if m: dis[int(m.group(1), 16)] = m.group(2)
tot = sum(d.values()); print(f"{fn}: {tot:.1f} instructions per node (steady state), {len(code)} words")
ents = sorted(pc for pc in tgb)   # call targets = function entries
fo = lambda pc: max([e for e in ents if e <= pc] or [0])
fs = collections.Counter()
for pc, v in d.items(): fs[fo(pc)] += v
print("per function (entry pc: instrs/node, calls/node):", ", ".join(f"{e:#x}: {v:.1f} ({(tgb[e]-tga[e])/dn:.1f})" for e, v in fs.most_common()))
mn = collections.Counter()
for pc, v in d.items(): mn[dis[pc].split()[0]] += v
print("mnemonic mix per node:", ", ".join(f"{m} {v:.1f}" for m, v in mn.most_common(12)))
ld_ = sum(v for m, v in mn.items() if m in ("ld", "lw", "lbu", "lb", "lhu")); st = sum(v for m, v in mn.items() if m in ("sd", "sw", "sb", "sh"))
print(f"loads {ld_:.1f} stores {st:.1f} (stack-frame traffic included)")
print("hottest pcs:")
for pc, v in sorted(d.items(), key=lambda x: -x[1])[:int(os.environ.get("TOP", 0))]: print(f"{pc:5x} x{v:<6.2f} {dis[pc]}")
open(p(f"trace_{fn}.txt"), "w").write("\n".join(f"{pc:5x} x{v:<6.2f} {dis[pc]}" for pc, v in sorted(d.items())))
