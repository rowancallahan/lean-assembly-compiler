#!/usr/bin/env python3
"""Self-run of `Legacy.Nano.SelfHost.binary` (NANO_MANIFEST "Self-run"). Sources: the nano corpus (CORPUS + INT_CORPUS), R random
UInt64 and R random Int64 programs, B large random programs. `emit_selfrun.lean` writes the PROVEN words (`binaryC`,
`binaryC_eq : binary = binaryC`), the words of its 2b and inliner components, and per source: expected = code of
`nanoCompileA (nanoElab src)`, the intermediate results, K0.
1. 2b and inliner alone on QEMU (input/expected from Lean): work W doubled until the stage's OOM flag is clear (the IR
   stages' flag is exact at memoryNeeded, Testing/asm/ir_test.py); then output, a1, a0, gp/sp, guards checked.
2. The linked binary on QEMU, work space5 K (Legacy/Nano/SelfHostFinal.lean), K = max(K0, W(2b), W(inliner)): output = expected,
   a1 = its length, a0 != -1, gp/sp restored, guards intact. One run per source (no retry).
3. Sail smoke on S sources (also: every write lands in the output or work block).
4. lexA alone (`nano_lexA`, expected `stage2a (lexB src)`, exact memoryNeeded) through ir_test.py: QEMU bulk + Sail.
usage (repo root): python3 Testing/nano/selfrun/selfrun_test.py [R] [B] [S] [seed]   (S = Sail smoke cases)"""
import os, random, re, shutil, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", "..", ".."))
A = os.path.join(ROOT, "Testing", "asm")
sys.path.insert(0, os.path.join(D, "..")); sys.path.insert(0, A)
from nanolib import *
R, B, S = (int(sys.argv[i]) if len(sys.argv) > i else d for i, d in ((1, 30), (2, 10), (3, 6)))
rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 11)

class Big(G):
    def program(s):
        r = s.rng; funs = []; out = []
        for i in range(r.randrange(3, 7)):
            ps = [f"p{j}" for j in range(r.randrange(1, 4))]
            out.append(f"def g{i} ({' '.join(ps)} : UInt64) : UInt64 := {s.expr(r.randrange(3, 6), ps, funs, False)}")
            funs.append((f"g{i}", len(ps)))
        return "\n".join(out)

W = os.path.join(D, "work"); shutil.rmtree(W, ignore_errors=True); os.makedirs(W)
srcs = list(CORPUS) + list(INT_CORPUS) + [G(rng).program() for _ in range(R)] + [GI(rng, "Int64").program() for _ in range(R)] \
     + [Big(rng).program() for _ in range(B)]
for i, s in enumerate(srcs): open(f"{W}/s{i:04}.nano", "wb").write(s.encode())
if os.environ.get("SKIP_EMIT") != "1":
    subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH NANO_DIR={W} /usr/bin/time -v timeout 30m lake env lean "
                   f"--tstack=4000000 Testing/nano/selfrun/emit_selfrun.lean", shell=True, check=True)

sys.argv = ["ir_test.py", "none", "0", "nano_self"]  # "none": import only
import ir_test as T
space5 = lambda K: 4 * (4 * (4 * (4 * K + 96) + 96) + 96) + 96
un = T.unhex
CASES = []
for l in open(os.path.join(A, "ir-words", "nano_self.cases")):
    f = l.split()
    if f: CASES.append(dict(src=un(f[0]), code=un(f[1]), K0=int(f[2]), dom=f[3] == "1", name=f[4], a=un(f[5]), s2=un(f[6]), i=un(f[7])))
assert len(CASES) > 0 and all(c["dom"] for c in CASES), "a source outside Domain K"
words = lambda nm: [int(l, 16) for l in open(os.path.join(A, "ir-words", nm + ".words")).read().split()[2:]]
asm_of = lambda ws: "".join(f"  .word 0x{w:08x}\n" for w in ws)
G_ = T.G
FLAG = 2 ** 64 - 1

def run(ws, runs, sail=False):
    """runs: (input, expected, work); per memory image (qemu, sail): per run (OOM flag a0 = -1, a0 = input address, a1,
    output ok, gp/sp ok, guards ok)"""
    lay, halt, base, tab, size = T.build([(x, y, W, True) for x, y, W in runs], asm_of(ws))
    qmem = T.qemu(halt, base, tab + T.E * len(runs) - base)
    mems = [qmem]
    if sail:
        subprocess.run(f"set -o pipefail; {T.SAIL} --inst-limit 40000000000 --trace-mem --trace-output /dev/stdout {T.p('crc.elf')}"
                       f" 2>&1 | grep -E 'mem\\[W|SUCCESS|FAIL|limit' > {T.p('sail.log')}", shell=True, executable="/bin/bash")
        out = open(T.p("sail.log")).read(); assert "SUCCESS" in out, out[-500:]
        smem = bytearray(open(T.p("crc.bin"), "rb").read()) + bytearray(qmem[size:])
        allowed = set(range(tab, tab + T.E * len(runs)))
        for (i0, o0, w0), (x, y, W) in zip(lay, runs):
            allowed |= set(range(base + o0, base + o0 + len(y))) | set(range(base + w0, base + w0 + W))
        for l in open(T.p("sail.log")):
            m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
            if not m: continue
            a, v = int(m.group(1), 16), m.group(2)
            if a < base: continue
            nb = len(v) // 2
            for j in range(nb):
                assert a + j in allowed, f"unexpected Sail write {l.strip()}"
                smem[a + j - base] = int(v[2 * (nb - 1 - j):2 * (nb - j)], 16)
        mems.append(smem)
    res = []
    for mem in mems:
        r = []
        for c, ((i0, o0, w0), (x, y, W)) in enumerate(zip(lay, runs)):
            e = tab - base + T.E * c
            gp, spo, a1, a0 = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56, 64, 72))
            guards = (list(mem[i0:i0 + len(x) + G_]) == x + [0xAA] * G_ and list(mem[o0 + len(y):o0 + len(y) + G_]) == [0xAA] * G_
                      and list(mem[w0 + W:w0 + W + G_]) == [0xAA] * G_)
            r.append((a0 == FLAG, a0 == base + i0, a1, bytes(mem[o0:o0 + len(y)]) == bytes(y), gp == T.MAGIC and spo == base + w0 + W, guards))
        res.append(r)
    return res

def batches(runs, lim=200 * 2 ** 20):
    b, t = [], 0
    for k, (x, y, W) in enumerate(runs):
        sz = len(x) + len(y) + W + 64
        if b and t + sz > lim: yield b; b, t = [], 0
        b.append(k); t += sz
    if b: yield b

# 1. the 2b and inliner stages alone: work doubled until the stage's flag is clear, then bisected (within 1/32)
def stage_runs(st, ws, fin, fout, ks, Wd):
    """runs the stage on the cases ks with work Wd[k]; returns the set of ks with the flag set; checks the others"""
    bad = set()
    runs = [(CASES[k][fin], CASES[k][fout], Wd[k]) for k in ks]
    for b in batches(runs):
        for j, r in zip(b, run(ws, [runs[j] for j in b])[0]):
            k = ks[j]
            if r[0]: bad.add(k); continue
            assert r[1] and r[2] == len(CASES[k][fout]) and r[3] and r[4] and r[5], (st, CASES[k]["name"], r)
    return bad
for st, ws, fin, fout in (("2b", words("nano_s2b"), "a", "s2"), ("inl", words("nano_sinl"), "s2", "i")):
    hi = {k: 8 * (len(c[fin]) + 64) for k, c in enumerate(CASES)}
    lo = {k: 0 for k in hi}
    todo, runs_n = list(hi), 0
    while todo:
        runs_n += 1; assert runs_n <= 24
        bad = stage_runs(st, ws, fin, fout, todo, hi)
        for k in bad: lo[k] = hi[k]; hi[k] *= 2
        todo = sorted(bad)
    while True:
        todo = [k for k in hi if hi[k] - lo[k] > max(64, hi[k] // 32)]
        if not todo: break
        runs_n += 1
        mid = {k: (lo[k] + hi[k]) // 16 * 8 for k in todo}
        bad = stage_runs(st, ws, fin, fout, todo, mid)
        for k in todo: (lo if k in bad else hi)[k] = mid[k]
    for k, c in enumerate(CASES): c["W" + st] = hi[k]
    print(f"stage {st} alone, QEMU: {len(CASES)}/{len(CASES)} ok in {runs_n} rounds ({len(ws)} words; every successful run "
          f"checked; work up to {max(hi.values())} bytes)", flush=True)
open(os.path.join(W, "stage_w.txt"), "w").write("".join(
    f"{c['name']} src {len(c['src'])} a {len(c['a'])} s2 {len(c['s2'])} i {len(c['i'])} K0 {c['K0']} W2b {c['W2b']} Winl {c['Winl']}\n" for c in CASES))
if os.environ.get("STAGES_ONLY") == "1": sys.exit(0)
# 2. the linked binary, one run per source whose work space5 K fits QEMU's 1 GB (ir_test.py: -m 1G)
LIM = int(os.environ.get("WORK_MAX", str(900 * 2 ** 20)))
wsB = T.words  # nano_self.words: binaryC
for c in CASES: c["K"] = max(c["K0"], c["W2b"], c["Winl"])
over = [c for c in CASES if space5(c["K"]) > LIM]
CASES = [c for c in CASES if space5(c["K"]) <= LIM]
runs = [(c["src"], c["code"], space5(c["K"])) for c in CASES]
ok = 0
for b in batches(runs):
    for k, r in zip(b, run(wsB, [runs[j] for j in b])[0]):
        assert not r[0] and r[2] == len(CASES[k]["code"]) and r[3] and r[4] and r[5], ("linked", CASES[k]["name"], r)
        ok += 1
print(f"not run linked (space5 K > {LIM} bytes): {[(c['name'], len(c['src']), c['K']) for c in over]}")
big = max(CASES, key=lambda c: len(c["src"]))
print(f"nano_self (linked binary) QEMU: {ok}/{len(CASES)} ok ({len(wsB)} words; sources up to {len(big['src'])} bytes, "
      f"outputs up to {max(len(c['code']) for c in CASES)} bytes; K {min(c['K'] for c in CASES)}..{max(c['K'] for c in CASES)}, "
      f"work space5 K up to {max(space5(c['K']) for c in CASES)} bytes)", flush=True)
open(os.path.join(W, "final.txt"), "w").write("".join(
    f"{c['name']} src {len(c['src'])} code {len(c['code'])} K0 {c['K0']} W2b {c['W2b']} Winl {c['Winl']} K {c['K']}\n" for c in CASES))
# 3. Sail smoke: the S//2 smallest works and the S - S//2 largest sources under SAIL_MAX bytes
SMAX = int(os.environ.get("SAIL_MAX", "400"))
by_w = sorted(range(len(CASES)), key=lambda k: CASES[k]["K"])
by_s = [k for k in sorted(range(len(CASES)), key=lambda k: -len(CASES[k]["src"])) if len(CASES[k]["src"]) <= SMAX]
sm = by_w[:S // 2] + [k for k in by_s if k not in by_w[:S // 2]][:S - S // 2]
ns = 0
for k in sm:
    q, sl = run(wsB, [runs[k]], sail=True)
    for r in (q[0], sl[0]):
        assert not r[0] and r[2] == len(CASES[k]["code"]) and r[3] and r[4] and r[5], ("linked sail", CASES[k]["name"], r)
    ns += 1
    print(f"  sail {CASES[k]['name']}: src {len(CASES[k]['src'])} B, code {len(CASES[k]['code'])} B ok", flush=True)
print(f"nano_self (linked binary) Sail: {ns}/{len(sm)} ok (QEMU == Sail == Lean, writes only in output + work)", flush=True)
shutil.rmtree(os.path.join(A, "ctest"), ignore_errors=True)
# 4. lexA alone
n = sum(1 for l in open(os.path.join(A, "ir-words", "nano_lexA.cases")) if l.strip())
subprocess.run(f"cd {A} && NOSAIL=1 python3 ir_test.py check {n} nano_lexA", shell=True, check=True)
subprocess.run(f"cd {A} && python3 ir_test.py check {S} nano_lexA", shell=True, check=True)
shutil.rmtree(os.path.join(A, "ctest"), ignore_errors=True)
