#!/usr/bin/env python3
"""Adversarial boundary fuzz for the subset rule (ROADMAP "Nano", owner): nano must be an EXACT subset of Lean.  Mutants of
valid programs (names replaced by keywords / Lean globals / odd shapes, inserted `-`, `--`, tabs, CR, `0x1`, `1e3`, `1_000`,
bare negative arguments `g -5`, duplicated defs, empty binder groups, mixed UInt64/Int64, deleted tokens, …) are judged by
BOTH sides, each mutant as its own root-level file (Lean: plain `lean`, Init only).  Failure = nano accepts and (Lean
rejects, or the meanings differ on random inputs).  `nano rejects, Lean accepts` is allowed and only counted.
usage: boundary.py [N mutants] [seed]"""
import os, random, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nanolib import *
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", ".."))
W = os.path.join(D, "work", "bnd"); os.makedirs(W, exist_ok=True)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
gu, gi = GI(rng, "UInt64"), GI(rng, "Int64")
NAMES = ["id", "at", "fun", "if", "by", "end", "cast", "flip", "rfl", "sorry", "this", "Type", "Nat", "_", "x_", "xA", "simp",
         "exact", "main", "max", "min", "not", "and", "or", "abc4", "incr", "a_b", "sq_1", "open", "show", "have", "from", "do",
         "ite", "bif", "mt", "bne", "in", "let", "def", "for", "mut", "try", "x1", "zz9", "q_12", "Int64", "UInt64", "pure", "get"]
INS = ["-", "--", "- -", "(", ")", "\t", "\r", "\r\n", " -5", "-5", "0x1", "1e3", "1_000", ";", ":=", "let", "UInt64", "Int64",
       "_", "+", "*", "/-c-/", "-- c\n", " - 7", "(-3)", "--5", "x", "\n", "007", "18446744073709551616", "-0"]
def tokens(s): return re.findall(r"\s+|\w+|:=|--|.", s)
def mutate(s):
    k = rng.randrange(9); t = tokens(s)
    if k == 0:  # rename one identifier occurrence (all occurrences sometimes)
        ids = sorted({x for x in t if re.fullmatch(r"[a-z]\w*", x) and x not in ("def", "let")})
        if ids:
            a, b = rng.choice(ids), rng.choice(NAMES)
            return re.sub(rf"\b{a}\b", b, s) if rng.random() < .6 else s.replace(a, b, 1)
    if k == 1 or k == 2:  # insert
        i = rng.randrange(len(t) + 1); return "".join(t[:i] + [rng.choice(INS)] + t[i:])
    if k == 3 and len(t) > 1:  # delete
        i = rng.randrange(len(t)); return "".join(t[:i] + t[i + 1:])
    if k == 4:  # duplicate a def line
        ls = s.split("\n"); i = rng.randrange(len(ls)); return "\n".join(ls[:i + 1] + [ls[i]] + ls[i + 1:])
    if k == 5:  # one type token swapped
        occ = [m.start() for m in re.finditer(r"\bU?Int64\b", s)]
        if occ:
            o = rng.choice(occ); w = "Int64" if s[o] == "U" else "UInt64"; e = re.match(r"U?Int64", s[o:]).end()
            return s[:o] + w + s[o + e:]
    if k == 6:  # a parenthesised argument made a bare negative numeral, or a numeral negated
        m = list(re.finditer(r"\(-?\d+\)|\b\d+\b", s))
        if m:
            x = rng.choice(m); return s[:x.start()] + "-" + x.group(0).strip("()-") + s[x.end():]
    if k == 7:  # empty / odd binder group
        return s.replace("(", rng.choice(["( ", "(x ", "() ("]), 1)
    return s.replace(" ", rng.choice(["", "  ", "\t", "\r\n", "\n", "\n "]), 1)
bases = list(CORPUS) + list(INT_CORPUS)
muts = []
while len(muts) < N:
    b = rng.choice(bases) if rng.random() < .5 else (gi if rng.random() < .5 else gu).program()
    m = b
    for _ in range(rng.choice([1, 1, 1, 2, 3])): m = mutate(m)
    muts.append(m)
def entry(s):
    ds = re.findall(r"^def\s+(\w+)((?:\s*\([^)]*\))*)\s*:", s, re.M)
    if not ds: return None, 0
    name, ps = ds[-1]; return name, sum(len(g.split(":")[0].split()) for g in re.findall(r"\(([^)]*)\)", ps))
cases = []
for i, m in enumerate(muts):
    open(f"{W}/m{i}.nano", "wb").write(m.encode())
    name, k = entry(m)
    signed_t = bool(re.search(r"\bInt64\b", m)) and not re.search(r"\bUInt64\b", m)
    ins = inputs_i(rng, k, 3) if signed_t else inputs(rng, k, 3)
    cases.append((name, k, signed_t, ins))
lst = []
for i, (name, k, st, ins) in enumerate(cases):
    for a in ins: lst.append(f"{W}/m{i}.nano " + " ".join(str(x % M) for x in a))
open(f"{W}/list.txt", "w").write("\n".join(lst) + "\n")
nano = subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH lake env lean --run Testing/nano/judge.lean {W}/list.txt",
                      shell=True, check=True, capture_output=True, text=True).stdout.split("\n")
def lean_judge(i):
    name, k, st, ins = cases[i]
    ev = ""
    if name:
        T = "Int64" if st else "UInt64"
        for a in ins: ev += f"\n#eval ({name} " + " ".join(f"({x} : {T})" for x in a) + ")"
    open(f"{W}/l{i}.lean", "wb").write(muts[i].encode() + ev.encode() + b"\n")
    r = subprocess.run(f"PATH=$HOME/.elan/bin:$PATH lean {W}/l{i}.lean", shell=True, capture_output=True, text=True, cwd=W)
    # the program part must have no error (errors in the appended #eval lines count as rejection too)
    return r.returncode == 0, [l for l in r.stdout.split("\n") if re.fullmatch(r"-?\d+", l.strip())]
with ThreadPoolExecutor(4) as ex: leanr = list(ex.map(lean_judge, range(N)))
pos = 0; acc_both = acc_lean_only = rej_both = 0; bad = []
for i, (name, k, st, ins) in enumerate(cases):
    nv = nano[pos:pos + len(ins)]; pos += len(ins)
    lok, louts = leanr[i]
    nacc = nv and nv[0] != "NONE"
    if not nacc:
        if lok: acc_lean_only += 1
        else: rej_both += 1
        continue
    if not lok: bad.append((muts[i], "nano accepts, Lean rejects")); continue
    want = [int(x) % M for x in louts]
    got = []
    for v in nv:
        if v == "ARITY": got.append(None); continue
        T, x = v.split(); got.append(int(x))
        if (T == "I") != st: bad.append((muts[i], f"type: nano {T}")); break
    if got != want: bad.append((muts[i], f"meaning nano {got} Lean {want}"))
    else: acc_both += 1
print(f"{N} mutants: both accept, same meaning {acc_both}; nano rejects, Lean accepts {acc_lean_only}; both reject {rej_both}; FAILURES {len(bad)}")
for m, why in bad[:20]: print("FAIL", why, repr(m))
assert not bad
