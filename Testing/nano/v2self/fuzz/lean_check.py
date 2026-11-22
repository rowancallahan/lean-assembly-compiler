#!/usr/bin/env python3
"""lean_check.py DIR SEED: STRICT check (owner rule: nano's language is a subset of Lean's) of fuzz_syntax.py results.
For EVERY program nano accepted (valid programs and accepted mutants), Lean must elaborate the EXACT text without any
error, and its `#eval` of `m` on the fuzz inputs must equal nano's QEMU outputs.  Any other outcome is a FAIL, classified:
PARSE (a parse error that is not layout), LAYOUT (Lean's offside rule: the same parse error with comments blanked),
TYPE (elaboration error, e.g. Lean defaulting a literal-only term to Nat), VALUE (different results).
Programs are batched 100 per file (one namespace each); a program with errors in a batch is re-checked alone.
Runs `lake env lean` from the repo root.  UNPROVEN test glue."""
import json, os, re, subprocess, sys
from multiprocessing import Pool
D, SEED = sys.argv[1], sys.argv[2]
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../../.."))
res = json.load(open(f"{D}/res_{SEED}.json"))

def okstat(s): return s.startswith("status 0") or s.startswith("status 1")

def lean(fn):
    p = subprocess.run(["lake", "env", "lean", "-DmaxErrors=1000000", fn], cwd=ROOT, capture_output=True, text=True, timeout=3600)
    return p.stdout + p.stderr

PARSE = ("unexpected", "unterminated", "expected ", "missing end", "invalid 'end'")
def parse_errors(out): return [l for l in out.split("\n") if "error:" in l and any(k in l.split("error:", 1)[1] for k in PARSE)]

def block_end(s, j):
    """the index after the dash-slash closing a nested block comment whose body starts at j (None: unterminated)"""
    d = 0
    while j < len(s):
        if s.startswith("-/", j):
            j += 2
            if d == 0: return j
            d -= 1
        elif s.startswith("/-", j): d += 1; j += 2
        else: j += 1
    return None

def strip(s):
    """blank out comments as the S lexer (= Lean) sees them: dash-dash lines; nested block comments; after a doc
    opener (slash-dash-dash, slash-dash-bang) Lean's whitespace, dash-dash lines and plain block comments are
    skipped before the nested body (LexSpec.docWs); columns kept"""
    o, i = [], 0
    while i < len(s):
        if s.startswith("--", i):
            j = s.find("\n", i); j = len(s) if j < 0 else j; o.append(" " * (j - i)); i = j
        elif s.startswith("/-", i):
            j = i + 2
            if s[j:j + 1] in ("-", "!"):
                j += 1
                while j < len(s):
                    if s[j] in " \n" or s.startswith("\r\n", j): j += 1
                    elif s.startswith("--", j):
                        k = s.find("\n", j); j = len(s) if k < 0 else k
                    elif s.startswith("/-", j) and s[j + 2:j + 3] not in ("-", "!"):
                        k = block_end(s, j + 2); j = len(s) if k is None else k
                    else: break
            k = block_end(s, j); j = len(s) if k is None else k
            o.append("".join(c if c == "\n" else " " for c in s[i:j])); i = j
        else: o.append(s[i]); i += 1
    return "".join(o)

def lean_one(r):
    fn = f"{D}/lean_{SEED}_one_{r['kind']}{r['i']}.lean"
    open(fn, "w").write(HDR + r["src"] + "\n")
    return lean(fn)

def errors(out): return [l for l in out.split("\n") if "error" in l.split(": ", 1)[-1][:12] or ": error" in l]

def classify(r):
    """the reason Lean rejects r alone (None: Lean accepts it)"""
    errs = errors(lean_one(r))
    if not errs: return None
    perr = parse_errors("\n".join(errs))
    if not perr: return "TYPE"
    fn = f"{D}/lean_{SEED}_one_{r['kind']}{r['i']}.s.lean"
    open(fn, "w").write(HDR + strip(r["src"]) + "\n")
    st = parse_errors(lean(fn))
    pos = lambda es: [e.split(".lean:", 1)[1].split(" error")[0] for e in es]
    return "LAYOUT" if pos(perr) == pos(st) else "PARSE"

def key(r): return r["i"] + (1000000 if r["kind"] != "valid" else 0)   # valid i and mutant i overlap

HDR = "import Nano.Main.Prelude\nset_option maxRecDepth 10000\nset_option maxErrors 100000\n\n"

def batch(items, tag):
    fn = f"{D}/lean_{SEED}_{tag}.lean"
    parts, rng, ln = [HDR.rstrip("\n"), ""], [], 4
    for r in items:
        n = r["src"].count("\n") + 1; rng.append((ln, ln + n, r)); ln += n; parts.append(r["src"])
    for r in items:
        for k, (inp, st, out) in enumerate(r["outs"]):
            parts.append(f"#eval ({key(r)}, {k}, {r['ns']}.m {inp})")
    open(fn, "w").write("\n".join(parts) + "\n")
    out = lean(fn)
    errl = set()
    for e in errors(out):
        try: errl.add(int(e.split(".lean:", 1)[1].split(":")[0]))
        except Exception: pass
    flagged = {id(r) for a, b, r in rng if any(a <= l < b for l in errl)}
    if any(l >= ln for l in errl): flagged = {id(r) for _, _, r in rng}   # an eval line failed: re-check all alone
    got = {}
    for m in re.finditer(r"\((\d+),\s*(\d+),\s*\[([0-9,\s]*)\]\)", out):
        got[(int(m[1]), int(m[2]))] = [int(x) for x in m[3].split(",") if x.strip()]
    res = []
    for _, _, r in rng:
        c = classify(r) if id(r) in flagged else None
        if c: res.append((c, r["kind"], r["i"])); continue
        for k, (inp, st, o) in enumerate(r["outs"]):
            if okstat(st) and got.get((key(r), k)) != o: res.append(("VALUE", r["kind"], r["i"], k, got.get((key(r), k)), o)); break
    return res

if __name__ == "__main__":
    acc = [r for r in res if (r["kind"] == "valid" and r["res"] == "ok") or (r["kind"] == "mut" and r["res"] == "accepted")]
    for r in acc:
        if r["kind"] == "mut": r["ns"] = r["ns"]          # mutants are rendered in namespace Mu<i>
    chunks = [acc[j:j + 100] for j in range(0, len(acc), 100)]
    with Pool(int(os.environ.get("JOBS", "4"))) as pool:
        out = pool.starmap(batch, [(c, f"b{j}") for j, c in enumerate(chunks)])
    bad = [b for o in out for b in o]
    from collections import Counter
    nv = sum(1 for r in acc if r["kind"] == "valid"); nm = len(acc) - nv
    nchk = sum(1 for r in acc for o in r["outs"] if okstat(o[1]))
    print(f"lean(strict): {nv} valid + {nm} accepted mutants, {nchk} runs; FAIL {len(bad)} {dict(Counter((b[0], b[1]) for b in bad))}")
    for b in bad: print("FAIL", str(b)[:300])
