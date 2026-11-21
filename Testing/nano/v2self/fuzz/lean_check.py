#!/usr/bin/env python3
"""lean_check.py DIR SEED: check (b)/(c) of fuzz_syntax.py: every accepted program's QEMU outputs equal Lean's own `#eval` of
its source (Prelude semantics).  Valid programs are batched (one namespace each); accepted mutants are elaborated one
per file (a mutant may break the surrounding file).  Runs `lake env lean` from the repo root.  UNPROVEN test glue."""
import json, os, re, subprocess, sys
from multiprocessing import Pool
D, SEED = sys.argv[1], sys.argv[2]
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../../.."))
res = json.load(open(f"{D}/res_{SEED}.json"))

def okstat(s): return s.startswith("status 0") or s.startswith("status 1")

def lean(fn):
    p = subprocess.run(["lake", "env", "lean", fn], cwd=ROOT, capture_output=True, text=True, timeout=3600)
    return p.stdout + p.stderr

PARSE = ("unexpected", "unterminated", "expected ", "missing end", "invalid 'end'")
def parse_errors(out): return [l for l in out.split("\n") if "error:" in l and any(k in l.split("error:", 1)[1] for k in PARSE)]

def batch(items, tag):
    """(b1) the exact NEW texts must have no Lean parse error; (b2) the Lean copies (`lsrc`, or the text itself for
    mutants) evaluate to the QEMU outputs"""
    fn = f"{D}/lean_{SEED}_{tag}.lean"
    parts = ["import Nano.V2Self.Prelude", "set_option maxRecDepth 10000", ""]
    for r in items: parts.append(r["src"])
    open(fn + ".exact.lean", "w").write("\n".join(parts) + "\n")
    perr = parse_errors(lean(fn + ".exact.lean"))
    parts = ["import Nano.V2Self.Prelude", "set_option maxRecDepth 10000", ""]
    for r in items: parts.append(r.get("lsrc", r["src"]))
    for r in items:
        nsl = r["ns"] + ("L" if "lsrc" in r else "")
        for k, (inp, st, out) in enumerate(r["outs"]):
            parts.append(f"#eval ({r['i']}, {k}, {nsl}.m {inp})")
    open(fn, "w").write("\n".join(parts) + "\n")
    got = {}
    for m in re.finditer(r"\((\d+),\s*(\d+),\s*\[([0-9,\s]*)\]\)", lean(fn)):
        got[(int(m[1]), int(m[2]))] = [int(x) for x in m[3].split(",") if x.strip()]
    bad = []
    for r in items:
        for k, (inp, st, out) in enumerate(r["outs"]):
            if not okstat(st): continue          # out of memory / capacity: Lean has no such stop
            if got.get((r["i"], k)) != out: bad.append((r["kind"], r["i"], k, got.get((r["i"], k)), out))
    return bad + [("PARSE", tag, e) for e in perr]

if __name__ == "__main__":
    valid = [r for r in res if r["kind"] == "valid" and r["res"] == "ok"]
    muts = [r for r in res if r["kind"] == "mut" and r["res"] == "accepted"]
    chunks = [valid[j:j + 150] for j in range(0, len(valid), 150)]
    jobs = [(c, f"v{j}") for j, c in enumerate(chunks)] + [([m], f"m{m['i']}") for m in muts]
    with Pool(int(os.environ.get("JOBS", "4"))) as pool:
        out = pool.starmap(batch, jobs)
    bad = [b for o in out for b in o]
    nchk = sum(1 for r in valid + muts for o in r["outs"] if okstat(o[1]))
    skipped = sum(1 for r in valid + muts for o in r["outs"] if not okstat(o[1]))
    print(f"lean: {len(valid)} valid + {len(muts)} accepted mutants, {nchk} runs compared, {skipped} capacity/OOM runs "
          f"skipped, {len(bad)} mismatches")
    for b in bad: print("MISMATCH", str(b)[:300])
