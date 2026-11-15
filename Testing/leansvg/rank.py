#!/usr/bin/env python3
"""rank.py /path/to/lean-svg: blocking features per lean-svg def (heuristic, from defs.json) and the greedy cumulative unlock order.
A def is `unlocked` when its own blocking features and those of everything it (transitively) calls are all provided.
Provided already (observed accepted: Orig.lean F1-F6, F13, F14, F17, F18, notes 9-19): scalar Nat/UIntN/Bool, if/match, ByteArray reads,
Option / tuple results, `for`/`Id.run` loops over ranges, fuel recursion, `*` `/` `%` by constants."""
import json, re, sys, os, glob, collections
D = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "defs.json")))
R = sys.argv[1]
types = set()
for f in glob.glob(R + "/LeanSvg/**/*.lean", recursive=True):
    for m in re.finditer(r"^\s*(?:structure|inductive|class)\s+(\w+)", open(f).read(), re.M): types.add(m.group(1))
ABB = {"Fx": "Int", "F32": "Nat"}
def feats(d):
    sig, _, body = d["body"].partition(":=")
    full = d["body"]
    F = set()
    if re.search(r"\bInt\b|\bFx\b|Int32|Int64|\.natAbs|Int\.", full): F.add("Int / Fx (signed)")
    if re.search(r"\bString\b|\bChar\b|s!\"|toString|\.toUTF8|\.toList\b", full): F.add("String / Char")
    if re.search(r"\bArray\b|#\[|\.getD\b|\.push\b|Array\.", sig + body) and not re.fullmatch(r"\s*", sig): F.add("Array (not ByteArray)")
    if re.search(r"ByteArray", full) and re.search(r"\.push\b|\.set!?\b|\.setIfInBounds|\.modify|\.extract|\+\+|emptyWithCapacity|mkEmpty|\.append|copySlice", body): F.add("ByteArray output (push/set/append)")
    if re.search(r"HashMap", full): F.add("HashMap")
    if re.search(r"\bfun\b|·|\.map\b|\.foldl|\.any\b|\.all\b|\.filter|\.find|\(p :|→ Bool\)|→ \w+\)", full): F.add("closures / higher-order")
    if re.search(r"(?<![\w.])(?:" + "|".join(sorted(types, key=len, reverse=True)) + r")(?![\w.])", sig) if types else False: F.add("structure / inductive values")
    if re.search(r"\bM\b|StateM|StateT|ExceptT|Id\.run do[^\n]*\n(?:.*\n)*?.*<-", full) and re.search(r"\bM\b\s", sig): F.add("StateM monad")
    # var-var mul/div/mod: operand after the operator is an identifier / paren, not a numeric literal
    if re.search(r"[\w)\]']\s*[*/%]\s*[A-Za-z(]", body) or re.search(r"[\w)\]']\s*[*/%]\s*\d+\s*[*/%]\s*[A-Za-z(]", body): F.add("variable * / % operand")
    if re.search(r"\bNat\.sqrt\b|\^|Nat\.log|\bpow\b", body): F.add("exponentiation / sqrt")
    if re.search(r"\bNat\b", sig) and re.search(r"[+*]|<<<", body): F.add("unbounded Nat contract (index/overflow bound)")
    return F
fe = {d["name"]: feats(d) for d in D}
by = {d["name"]: d for d in D}
def closure(n, seen=None):
    seen = seen if seen is not None else set()
    if n in seen: return seen
    seen.add(n)
    for c in by[n]["calls"]:
        if c in by: closure(c, seen)
    return seen
cf = {n: set().union(*(fe[m] for m in closure(n))) for n in by}
data = re.compile(r"Fonts|Data|Table|Stix")
def run(subset, title):
    names = [n for n in subset]
    unlocked, order, got = set(), [], set()
    total = len(names)
    def cnt(G): return sum(1 for n in names if cf[n] <= G)
    allF = set().union(*(cf[n] for n in names))
    print(f"\n### {title}: {total} defs\n")
    print(f"already unlocked with no new feature: {cnt(set())}\n")
    print("| step | feature added | newly unlocked | cumulative | % of defs |\n|---|---|---|---|---|")
    G = set(); prev = cnt(G); step = 0
    while G != allF:
        best = max(allF - G, key=lambda f: (cnt(G | {f}), f)); G |= {best}; step += 1
        c = cnt(G); print(f"| {step} | {best} | +{c - prev} | {c} | {100 * c // total}% |"); prev = c
    print("\nsingle-feature blocking (defs whose only missing feature is it):")
    single = collections.Counter(next(iter(cf[n])) for n in names if len(cf[n]) == 1)
    print("; ".join(f"{k}: {v}" for k, v in single.most_common()))
    print("\nfeature frequency (defs needing it, incl. via callees):")
    fr = collections.Counter(f for n in names for f in cf[n]); print("; ".join(f"{k}: {v}" for k, v in fr.most_common()))
run([d["name"] for d in D if not data.search(d["mod"])], "lean-svg without generated data files")
run([d["name"] for d in D if not data.search(d["mod"]) and d["level"] == 0], "leaves only (level 0, no data files)")
