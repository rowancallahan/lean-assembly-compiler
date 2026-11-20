"""Tiny RV64IM tracer for g41 code (debugging B2/B3 crashes).  usage: [TR=word,count] [STOP=word] [HEAD=word,delta] rvtrace.py WORDS_FILE INPUT_FILE [WORK_MB=80] [N]
Convention as selfrun.py; on a bad pc prints the last N instructions with s0/t6/ra."""
import sys, collections
M = (1 << 64) - 1
def sx(v, b): v &= (1 << b) - 1; return v - (1 << b) if v >> (b - 1) else v
words = [int(x, 16) for x in open(sys.argv[1]).read().split()[2:]]
inp = open(sys.argv[2], "rb").read()
WK = int(sys.argv[3]) << 20 if len(sys.argv) > 3 else 80 << 20
CODE, INP, OUT, WORK, RET = 0x80000000, 0x90000000, 0x98000000, 0xA0000000, 0x7FFFF000
mem = bytearray(WK); inb = bytearray(inp) + bytearray(16); out = bytearray(1 << 20)
def region(a, n):
    if WORK <= a and a + n <= WORK + WK: return mem, a - WORK
    if INP <= a and a + n <= INP + len(inb): return inb, a - INP
    if OUT <= a and a + n <= OUT + len(out): return out, a - OUT
    raise Exception(f"bad mem access {a:#x}")
def ld(a, n): b, o = region(a, n); return int.from_bytes(b[o:o+n], "little")
def st(a, n, v): b, o = region(a, n); b[o:o+n] = (v & ((1 << 8*n) - 1)).to_bytes(n, "little")
x = [0] * 32
x[1] = RET; x[2] = WORK + WK; x[10] = INP; x[11] = len(inp); x[12] = WORK; x[13] = OUT
import os
TR = [int(v) for v in os.environ['TR'].split(',')] + [0] if 'TR' in os.environ else None
STOP = int(os.environ['STOP']) if 'STOP' in os.environ else None
HEAD = [int(v) for v in os.environ['HEAD'].split(',')] if 'HEAD' in os.environ else None
HV = [0]
pc = CODE; hist = collections.deque(maxlen=400); n = 0
while pc != RET:
    i = (pc - CODE) >> 2
    if not (0 <= i < len(words)) or pc & 3: print("BAD PC", hex(pc)); break
    w = words[i]; hist.append((i, w, x[8], x[31], x[1])); n += 1
    if HEAD is not None and i == HEAD[0]:
        dlt = x[31] - x[8]
        if dlt != HEAD[1]:
            print("drift at visit", HV[0], "t6-s0 =", dlt); [print(f"  w{j} {ww:08x} s0={a:#x} t6={b:#x} ra={c:#x}") for j, ww, a, b, c in list(hist)[-int(os.environ.get('NH','60')):]]; sys.exit(0)
        HV[0] += 1
    if STOP is not None and i == STOP:
        [print(f"  w{j} {ww:08x} s0={a:#x} t6={b:#x} ra={c:#x}") for j, ww, a, b, c in list(hist)[-40:]]; sys.exit(0)
    if TR is not None:
        if i == TR[0] and TR[2] == 0: TR[2] = 1
        if TR[2] and TR[1] > 0: TR[1] -= 1; print(f"  w{i} {w:08x} s0={x[8]:#x} t6={x[31]:#x} t0={x[5]:#x} t1={x[6]:#x}")
    op = w & 127; rd = (w >> 7) & 31; f3 = (w >> 12) & 7; r1 = (w >> 15) & 31; r2 = (w >> 20) & 31; f7 = w >> 25
    a, b = x[r1], x[r2]; npc = pc + 4; v = None
    if op == 0x13:
        im = sx(w >> 20, 12)
        if f3 == 0: v = a + im
        elif f3 == 1: v = a << (im & 63)
        elif f3 == 5: v = (a >> (im & 63)) if not (w >> 30) & 1 else sx(a, 64) >> (im & 63)
        elif f3 == 4: v = a ^ im
        elif f3 == 6: v = a | im
        elif f3 == 7: v = a & im
        elif f3 == 3: v = int(a < (im & M))
        elif f3 == 2: v = int(sx(a, 64) < im)
    elif op == 0x33:
        if f7 == 1 and f3 == 0: v = a * b
        elif f7 == 1 and f3 == 3: v = (a * b) >> 64
        elif f3 == 0: v = a - b if f7 == 32 else a + b
        elif f3 == 1: v = a << (b & 63)
        elif f3 == 5: v = (a >> (b & 63)) if f7 == 0 else sx(a, 64) >> (b & 63)
        elif f3 == 4: v = a ^ b
        elif f3 == 6: v = a | b
        elif f3 == 7: v = a & b
        elif f3 == 3: v = int(a < b)
        elif f3 == 2: v = int(sx(a, 64) < sx(b, 64))
    elif op == 0x37: v = sx(w & 0xFFFFF000, 32)
    elif op == 0x17: v = pc + sx(w & 0xFFFFF000, 32)
    elif op == 0x03:
        ad = (a + sx(w >> 20, 12)) & M
        v = ld(ad, 8) if f3 == 3 else ld(ad, 1) if f3 == 4 else None
    elif op == 0x23:
        ad = (a + sx(((w >> 25) << 5) | ((w >> 7) & 31), 12)) & M
        st(ad, 8 if f3 == 3 else 1, b)
    elif op == 0x63:
        im = sx(((w >> 31) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 63) << 5) | (((w >> 8) & 15) << 1), 13)
        c = {0: a == b, 1: a != b, 4: sx(a, 64) < sx(b, 64), 5: sx(a, 64) >= sx(b, 64), 6: a < b, 7: a >= b}[f3]
        if c: npc = pc + im
    elif op == 0x6F:
        im = sx(((w >> 31) << 20) | (((w >> 12) & 255) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 1023) << 1), 21)
        v = pc + 4; npc = pc + im
    elif op == 0x67: v = pc + 4; npc = (a + sx(w >> 20, 12)) & ~1 & M
    if v is None and op not in (0x23, 0x63): print("UNKNOWN", hex(w), "at", i); break
    if rd and v is not None: x[rd] = v & M
    pc = npc & M
else:
    print(f"returned: a0={sx(x[10],64)} a1={x[11]} steps={n}"); open(sys.argv[2] + ".out", "wb").write(out[:x[11]] if x[10] == 0 else b"")
    sys.exit(0)
print("steps", n); [print(f"  w{i} {w:08x} s0={s0:#x} t6={t6:#x} ra={ra:#x}") for i, w, s0, t6, ra in list(hist)[-int(sys.argv[4] if len(sys.argv)>4 else 25):]]
