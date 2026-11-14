#!/usr/bin/env python3
"""Generator (d): merge sort / insertion sort machine code on adversarial inputs -> fuzz_run.py case file.
usage: gen_sort.py SEED OUT [--exhaustive MAXLEN] [--random N MAXLEN] [--mutate word|exp]
 exhaustive: every length 0..MAXLEN for 6 patterns (random, sorted, reversed, all-equal, two values, sawtooth);
 random: N inputs of random length up to MAXLEN (random/patterned bytes), stack pointer misalignment 0..7."""
import os, random, sys
D = os.path.dirname(os.path.abspath(__file__))
seed = int(sys.argv[1]); out = sys.argv[2]; a = sys.argv[3:]
rng = random.Random(seed)
words = lambda n: [l.strip() for l in open(os.path.join(D, "arr-words", n + ".words")) if l.strip()]
def pat(k, L):
    if k == 0: return [rng.randrange(256) for _ in range(L)]
    if k == 1: return sorted(rng.randrange(256) for _ in range(L))
    if k == 2: return sorted((rng.randrange(256) for _ in range(L)), reverse=True)
    if k == 3: return [rng.randrange(256)] * L
    if k == 4: return [rng.choice([0, 255]) for _ in range(L)]
    return [(i * 37 + seed) % 256 for i in range(L)]
ins = []   # (xs, mis)
if "--exhaustive" in a:
    m = int(a[a.index("--exhaustive") + 1])
    ins += [(pat(k, L), rng.randrange(8)) for L in range(m + 1) for k in range(6)]
if "--random" in a:
    i = a.index("--random"); n, m = int(a[i + 1]), int(a[i + 2])
    ins += [(pat(rng.randrange(6), rng.choice([rng.randrange(m + 1), rng.randrange(40), m])), rng.randrange(8)) for _ in range(n)]
mut = a[a.index("--mutate") + 1] if "--mutate" in a else None
f = open(out, "w"); B = 40
for name, w, a2, frame, maxl in (("msort", "msort", "scr", 64, 10**9), ("insertion", "sort", "junk", 0, 800)):
    ws = words(w)
    if mut == "word": ws[len(ws) // 2] = "%08x" % (int(ws[len(ws) // 2], 16) ^ 0x00100000)
    use = [x for x in ins if len(x[0]) <= maxl]
    for j in range(0, len(use), B):
        f.write(f"prog {name}_{j // B}\nkind blk\nwords {' '.join(ws)}\na2 {a2}\nframe {frame}\n")
        for xs, mis in use[j:j + B]:
            e = sorted(xs)
            if mut == "exp" and e: e[len(e) // 2] ^= 1
            f.write(f"in i={bytes(xs).hex() or '-'} e={bytes(e).hex() or '-'} sp={len(xs)} ss={len(xs) if name == 'msort' else 0} mis={mis}\n")
