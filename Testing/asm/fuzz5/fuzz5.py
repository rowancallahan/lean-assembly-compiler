#!/usr/bin/env python3
"""FUZZ5: random differential tests of `frontx_ind` entries (`frontx-words/<fn>.words`, first line `ind A B L`) against
executed Lean (`ref.lean`, `lean --run`, verbatim source functions) and an independent Python reference.
usage: fuzz5.py FN SEED NCASES [qemu|sail] [big]   (env: FILL=seed; SAILN=cases for sail; BIG=1 adds large inputs)
Per case: [G in G][out R G][pad][G work WK G] (R = result length, WK = A + B n exactly), output pre-filled with random bytes,
work block random-filled; QEMU is run twice with different fills.  Checks: output == Lean == Python; a1 == R for tree
results; gp/sp; all guards (also below the work block); the whole QEMU memory image outside output+work+result slots equals
the initial image; Sail: every write lands in output or work block; slack (bytes the program never wrote between heap and
stack; found by comparing the final work blocks of the two fills) > 0."""
import os, random, re, subprocess, sys, threading
sys.setrecursionlimit(10 ** 7); threading.stack_size(1 << 30)
D = os.path.dirname(os.path.abspath(__file__)); WD = os.path.join(D, "..", "frontx-words")
W = os.path.join(D, "work"); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
LEAN = [d for d in __import__("glob").glob("/tmp/leandl/x/*/bin")][0] + "/lean"
M64 = 2 ** 64; G = 16; E = 72
sh = lambda c: subprocess.run(c, shell=True, check=True)
le = lambda x: (x % M64).to_bytes(8, "little")
EDGE = [0, 1, 2, 127, 128, 255, 256, 2 ** 31, 2 ** 32 - 1, 2 ** 32, 2 ** 63 - 1, 2 ** 63, 2 ** 63 + 1, M64 - 2, M64 - 1]
def scal(r):
    k = r.random()
    return r.choice(EDGE) if k < .5 else r.randrange(M64) if k < .8 else r.randrange(300)
# ---- values: tree = None | (l, x, r); pos = n >= 0 (succ count); list = python list; level = ('z',) | ('s',u) | ('m',a,b) | ('i',a,b) | ('p',)
def enc_tree(t):
    o = bytearray(); st = [t]
    while st:
        t = st.pop()
        if isinstance(t, int): o += le(t); continue
        if t is None: o.append(0); continue
        o.append(1); l, x, rr = t; st += [rr, x, l]       # order: l, x, r
    return bytes(o)
enc_pos = lambda n: b"\x01" * n + b"\x00"
enc_list = lambda xs: b"".join(b"\x01" + le(x) for x in xs) + b"\x00"
def enc_level(v):
    o = bytearray(); st = [v]
    while st:
        v = st.pop(); o.append("zsmip".index(v[0])); st += list(reversed(v[1:]))
    return bytes(o)
def count(t):
    n = 0; st = [t]
    while st:
        t = st.pop()
        if t: n += 1; st += [t[0], t[2]]
    return n
def mirror(t):
    def f(t): return None if t is None else (f(t[2]), t[1], f(t[0]))
    return f(t)
def graft(a, b):
    if a is None: return b
    spine = []; t = a
    while t is not None: spine.append(t); t = t[0]
    res = b
    for t in reversed(spine): res = (res, t[1], t[2])
    return res
def hasparam(v):
    st = [v]
    while st:
        v = st.pop()
        if v[0] == 'p': return True
        st += list(v[1:])
    return False
def neverzero(v):
    while True:
        if v[0] in 'zp': return False
        if v[0] == 's': return True
        if v[0] == 'm':                       # isNeverZero l || isNeverZero r
            return neverzero(v[1]) or neverzero(v[2])
        v = v[2]                              # imax _ r
# fn -> (generator kind, retLen, python reference: values -> bytes)
KIND = {"bt_count": "tree", "bt_mirror": "tree", "bt_graftleft": "tree2", "pos_tonat": "pos", "pos_plus": "pos2",
        "nontail_sum_ln": "list", "tail_sum_ln": "list", "tail_reverse_ln": "list", "list_append_ln": "list2",
        "level_hasparam": "level", "level_isneverzero": "level"}
def pyref(fn, vs):
    if fn == "bt_count": return le(count(vs[0]))
    if fn == "bt_mirror": return enc_tree(mirror(vs[0]))
    if fn == "bt_graftleft": return enc_tree(graft(*vs))
    if fn == "pos_tonat": return le(vs[0] + 1)
    if fn == "pos_plus": return enc_pos(vs[0] + 1 + vs[1])
    if fn in ("nontail_sum_ln", "tail_sum_ln"): return le(sum(vs[0]))
    if fn == "tail_reverse_ln": return enc_list(vs[0][::-1])
    if fn == "list_append_ln": return enc_list(vs[0] + vs[1])
    if fn == "level_hasparam": return bytes([hasparam(vs[0])])
    if fn == "level_isneverzero": return bytes([neverzero(vs[0])])
# ---- generators (size = node/element count; `shape`: random, left, right, zig, wide, perfect, comb)
def gen_tree(r, n, shape=None):
    shape = shape or r.choice(["random", "random", "left", "right", "zig", "wide", "comb"])
    sc = lambda: scal(r)
    if n == 0: return None
    if shape == "left" or shape == "right" or shape == "zig":
        t = None
        for i in range(n):
            left = shape == "left" or (shape == "zig" and i % 2 == 0)
            t = (t, sc(), None) if left else (None, sc(), t)
        return t
    if shape == "comb":                               # spine with a leaf-child pair at each node
        t = None
        for i in range(n): t = ((t, sc(), (None, sc(), None)) if i % 2 else ((None, sc(), None), sc(), t)) if i else (None, sc(), None)
        return t
    if shape == "wide":                               # perfect-ish, breadth first
        nodes = [[None, sc(), None] for _ in range(n)]
        for i in range(n):
            for k, j in ((0, 2 * i + 1), (2, 2 * i + 2)):
                if j < n: nodes[i][k] = nodes[j]
        def freeze(i):                                # iterative bottom-up
            res = {}
            for i in range(n - 1, -1, -1):
                l = res.get(2 * i + 1); rr = res.get(2 * i + 2); res[i] = (l, nodes[i][1], rr)
            return res[0]
        return freeze(0)
    # random: split n-1 by a random (skewed) point iteratively
    root = [None, sc(), None]; todo = [(root, n - 1)]
    while todo:
        node, m = todo.pop()
        if m == 0: continue
        a = r.choice([0, m - 1, r.randrange(m)]) if r.random() < .5 else r.randrange(m)
        for k, sz in ((0, a), (2, m - 1 - a)):
            if sz > 0: c = [None, sc(), None]; node[k] = c; todo.append((c, sz))
    def freeze2(node):
        order = []; st = [node]
        while st:
            x = st.pop(); order.append(x)
            for k in (0, 2):
                if x[k] is not None: st.append(x[k])
        res = {}
        for x in reversed(order):
            res[id(x)] = (res.get(id(x[0])) if x[0] is not None else None, x[1], res.get(id(x[2])) if x[2] is not None else None)
        return res[id(node)]
    return freeze2(root)
def gen_list(r, n): return [scal(r) for _ in range(n)]
def gen_level(r, n):
    if n <= 0: return r.choice([('z',), ('p',)])
    shape = r.choice(["chain", "rand", "right"])
    leaf = lambda: r.choice([('z',), ('p',)])
    if shape == "chain":
        v = leaf()
        for _ in range(n): v = ('s', v) if r.random() < .8 else ('m' if r.random() < .5 else 'i', v, leaf())
        return v
    if shape == "right":
        v = leaf()
        for _ in range(n): v = (r.choice('mi'), leaf(), v)
        return v
    def g(k): return leaf() if k <= 0 else (lambda c: (c, g(k - 1)) if c == 's' else (c, g(r.randrange(k)), g(r.randrange(k))))(r.choice("smi"))
    return g(min(n, 400))
def gen_values(r, kind, n, shape=None):
    one = {"tree": lambda: gen_tree(r, n, shape), "pos": lambda: n, "list": lambda: gen_list(r, n), "level": lambda: gen_level(r, n)}
    k = kind.rstrip("2"); one = {"tree": lambda m: gen_tree(r, m, shape), "pos": lambda m: m, "list": lambda m: gen_list(r, m),
                                 "level": lambda m: gen_level(r, m)}[k]
    if kind.endswith("2"):
        a = r.choice([0, n, r.randrange(n + 1)]) if n else 0
        return [one(a), one(n - a if r.random() < .8 else r.randrange(n + 1))]
    return [one(n)]
ENC = {"tree": enc_tree, "pos": enc_pos, "list": enc_list, "level": enc_level}
def gen_cases(fn, seed, N, big):
    r = random.Random(f"{fn}/{seed}"); kind = KIND[fn]; out = []
    sizes = [0, 1, 2, 3] + [r.choice([4, 5, 8, 16, 31, 32, 33, 64, 100]) for _ in range(6)]
    while len(sizes) < N: sizes.append(r.choice([r.randrange(1, 30), r.randrange(1, 200), r.randrange(1, 1000)]))
    shapes = [None] * len(sizes)
    if kind.startswith("tree"):
        for i, s in enumerate(["left", "right", "zig", "wide", "comb"]): shapes[4 + i] = s
    for n, s in zip(sizes, shapes): out.append(gen_values(r, kind, n, s))
    if big:    # degenerate chains / wide trees up to the space bound's range (input bytes about 0.5-2 MB QEMU only)
        for n, s in [(20000, "left"), (20000, "right"), (30000, "zig"), (60000, "wide"), (60000, "random"), (150000, "left")] if kind.startswith("tree") else \
                    [(40000, None), (120000, None), (200000, None)]:
            out.append(gen_values(r, kind, n if kind != "level" else min(n, 40000), s))
    return out
def enc_vals(kind, vs): return b"".join(ENC[kind.rstrip("2")](v) for v in vs)
# ---- Lean
def lean_results(fn, ins):
    open(os.path.join(W, f"{fn}.in"), "w").write("".join(f"{fn} {x.hex()}\n" for x in ins))
    p = subprocess.run(f"ulimit -s unlimited; {LEAN} --run {D}/ref.lean < {W}/{fn}.in", shell=True, capture_output=True, text=True, executable="/bin/bash")
    assert p.returncode == 0, p.stderr[-2000:]
    outs = p.stdout.split("\n")[:-1]; assert len(outs) == len(ins), p.stderr[-500:]
    return [bytes.fromhex(o) for o in outs]
# ---- machine
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
DRIVER = """.section .text.start
.globl _start
_start: lla s0, tab
  li s2, %d
1: ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  ld sp, 32(s0)
  ld gp, 40(s0)
  jal ra, func
  sd gp, 48(s0)
  sd sp, 56(s0)
  sd a1, 64(s0)
  addi s0, s0, %d
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
func:
%s.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
"""
MAGIC = 0x0123456789ABCDEF
def build(fn, cases, A, B, fill, tag):
    """layout per case: G in G | out R G | pad | G work WK G ; returns lay, symbols"""
    rf = random.Random(f"fill{fill}"); words = [int(l, 16) for l in open(f"{WD}/{fn}.words").read().split("\n")[1:] if l.strip()]
    data = bytearray(); tab = []; lay = []
    for xs, ys in cases:
        n, R = len(xs), len(ys); WK = A + B * n
        o = len(data) + G; i0 = o; o0 = i0 + n + G; w0 = (o0 + R + G + G + 7) // 8 * 8
        lay.append((i0, o0, w0, WK, n, R))
        rb = lambda k: rf.randbytes(k)
        data += b"\xAA" * G + xs + b"\xAA" * G + rb(R) + b"\xAA" * G
        data += b"\xAA" * (w0 - G - len(data)) + b"\xAA" * G if False else b""
        data += b"\xAA" * (w0 - len(data) - G) + b"\xAA" * G + rb(WK) + b"\xAA" * G
        base_rel = 0
        tab.append((i0, n, w0, o0, w0 + WK))
    open(f"{W}/{tag}.bin", "wb").write(data)
    func = "".join(f"  .word 0x{w:08x}\n" for w in words)
    ent = "\n".join(f"  .quad base+{a}, {b}, base+{c}, base+{d}, base+{e}, {MAGIC}, 0, 0, 0" for a, b, c, d, e in tab)
    open(f"{W}/{tag}.S", "w").write(DRIVER % (len(cases), E, func) + f'.data\n.align 4\nbase:\n.incbin "{W}/{tag}.bin"\n.align 3\ntab:\n{ent}\n')
    open(f"{W}/m.ld", "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{W}/m.ld -Wl,--no-relax -Wl,--build-id=none {W}/{tag}.S -o {W}/{tag}.elf")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {W}/{tag}.elf", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    return lay, sym("halt"), sym("base"), sym("tab"), len(data), bytes(data)
def qemu(tag, halt, a, n):
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 2G -bios {W}/{tag}.elf -display none -serial none -monitor stdio",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version")
    while "pc       %016x" % halt not in hmp("info registers"): pass
    hmp(f'pmemsave {a:#x} {n} "{W}/{tag}.q"'); q.stdin.write("quit\n"); q.wait()
    return open(f"{W}/{tag}.q", "rb").read()
def check_batch(fn, cases, A, B, retlen, fill, target, stats):
    tag = f"{fn}_{target}"
    lay, halt, base, tab, size, init = build(fn, cases, A, B, fill, tag)
    mems = []
    lay2, _, _, _, _, init2 = build(fn, cases, A, B, fill + 1000, tag + "b") if target == "qemu" else (None,) * 6
    if target == "qemu":
        mems = [(qemu(tag, halt, base, tab + E * len(cases) - base), init), (qemu(tag + "b", halt, base, tab + E * len(cases) - base), init2)]
    else:
        r = subprocess.run(f"{SAIL} --inst-limit 4000000000 --trace-mem --trace-output {W}/{tag}.log {W}/{tag}.elf", shell=True, capture_output=True, text=True)
        assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
        allowed = set(range(tab, tab + E * len(cases)))
        for (i0, o0, w0, WK, n, R) in lay: allowed |= set(range(base + o0, base + o0 + R)) | set(range(base + w0, base + w0 + WK))
        smem = bytearray(init) + bytearray(b"\0" * (E * len(cases) + tab - base - size))
        for l in open(f"{W}/{tag}.log"):
            m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
            if not m: continue
            a, v = int(m.group(1), 16), m.group(2)
            if a < base: continue
            nb = len(v) // 2
            for j in range(nb):
                assert a + j in allowed, f"unexpected Sail write {l.strip()}"
                smem[a + j - base] = int(v[2 * (nb - 1 - j):2 * (nb - j)], 16)
        os.remove(f"{W}/{tag}.log")
        mems = [(bytes(smem), init)]
    for (mem, ini), (xs, ys), (i0, o0, w0, WK, n, R) in zip(mems[0:1] * 0 or [None] * 0, [], []): pass
    for mi, (mem, ini) in enumerate(mems):
        outl = lambda c: None
        # whole-image comparison outside output/work/result slots
        mask = bytearray(b"\1" * (tab - base))
        for (i0, o0, w0, WK, n, R) in lay:
            for k in range(o0, o0 + R): mask[k] = 0
            for k in range(w0, w0 + WK): mask[k] = 0
        diff = [k for k in range(tab - base) if mask[k] and mem[k] != ini[k]] if len(ini) >= tab - base else []
        if target == "qemu":
            # fast path: compare per region
            pass
        for c, ((xs, ys), (i0, o0, w0, WK, n, R)) in enumerate(zip(cases, lay)):
            got = bytes(mem[o0:o0 + R]); assert got == ys, (target, fn, "OUTPUT", n, got[:64].hex(), ys[:64].hex(), "reproducer", xs.hex() if n < 400 else f"len {n}")
            assert mem[i0 - G:i0 + n + G] == b"\xAA" * G + xs + b"\xAA" * G, (target, fn, "input/guard", n)
            assert mem[o0 + R:o0 + R + G] == b"\xAA" * G, (target, fn, "output guard", n)
            assert mem[w0 - G:w0] == b"\xAA" * G and mem[w0 + WK:w0 + WK + G] == b"\xAA" * G, (target, fn, "work guard", n)
            e = tab - base + E * c
            gp, spo, a1 = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56, 64))
            assert gp == MAGIC and spo == base + w0 + WK, (target, fn, "gp/sp", n)
            if retlen: assert a1 == R, (target, fn, "a1", n, a1, R)
        # bytes outside out/work/slots: compare ranges between regions
        prev = 0
        for (i0, o0, w0, WK, n, R) in lay:
            for lo, hi in ((prev, o0), (o0 + R, w0), ):
                assert mem[lo:hi] == ini[lo:hi], (target, fn, "memory outside output/work changed", lo, hi)
            prev = w0 + WK
        assert mem[prev:tab - base] == ini[prev:tab - base], (target, fn, "tail changed")
    if target == "qemu":
        (m1, _), (m2, _) = mems
        for (i0, o0, w0, WK, n, R), (xs, ys) in zip(lay, cases):
            # bytes equal in both fills = written (or false-equal, 1/256); slack = longest run of unwritten bytes
            a, b = m1[w0:w0 + WK], m2[w0:w0 + WK]
            best = cur = 0
            for k in range(WK):
                cur = cur + 1 if a[k] != b[k] else 0; best = max(best, cur)
            used = sum(1 for k in range(WK) if a[k] == b[k])
            stats.append((n, WK, best, used, fn))
            assert best > 0 or WK < 64, (target, fn, "no slack: heap and stack may have met", n)
def main():
    fn, seed, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); target = sys.argv[4] if len(sys.argv) > 4 else "qemu"
    big = len(sys.argv) > 5 or os.environ.get("BIG") == "1"
    ind = open(f"{WD}/{fn}.words").readline().split(); A, B, retlen = int(ind[1]), int(ind[2]), int(ind[3])
    kind = KIND[fn]; vals = gen_cases(fn, seed, N, big)
    ins = [enc_vals(kind, v) for v in vals]
    outs = lean_results(fn, ins)
    for v, x, y in zip(vals, ins, outs): assert pyref(fn, v) == y, ("Lean != Python", fn, x.hex()[:200], y.hex()[:100], pyref(fn, v).hex()[:100])
    if os.environ.get("CORRUPT"): outs[-1] = bytes([outs[-1][0] ^ 1]) + outs[-1][1:]   # harness sanity: must fail
    cases = list(zip(ins, outs)); stats = []
    budget = 300 * 2 ** 20; batch = []; tot = 0; nb = 0
    def flush():
        nonlocal batch, tot, nb
        if batch: check_batch(fn, batch, A, B, retlen, int(os.environ.get("FILL", seed)) + nb, target, stats); nb += 1
        batch = []; tot = 0
    for c in cases:
        sz = len(c[0]) * (1 + B) + A + len(c[1]) + 100
        if tot + sz > budget: flush()
        batch.append(c); tot += sz
    flush()
    mn = min(s[2] / s[1] for s in stats) if stats else None
    print(f"{fn}: {len(cases)} cases ok on {target} (seed {seed}; max input {max(len(c[0]) for c in cases)} bytes; max out {max(len(c[1]) for c in cases)}" +
          (f"; min slack {min(s[2] for s in stats)} bytes = {mn:.3f} of the work block, max used fraction {max(s[3] / s[1] for s in stats):.3f})" if stats else ")"))
t = threading.Thread(target=main); t.start(); t.join()
