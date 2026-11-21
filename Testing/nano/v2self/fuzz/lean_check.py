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

def strip(s):
    """blank out comments as the S lexer sees them (LexSpec: nested block comments, dash-dash lines), keeping columns"""
    o, i = [], 0
    while i < len(s):
        if s.startswith("--", i):
            j = s.find("\n", i); j = len(s) if j < 0 else j; o.append(" " * (j - i)); i = j
        elif s.startswith("/-", i):
            d, j = 0, i + 2
            while j < len(s):
                if s.startswith("-/", j):
                    j += 2
                    if d == 0: break
                    d -= 1
                elif s.startswith("/-", j): d += 1; j += 2
                else: j += 1
            o.append("".join(c if c == "\n" else " " for c in s[i:j])); i = j
        else: o.append(s[i]); i += 1
    return "".join(o)

def layout_only(r, tag):
    """a Lean parse error in a valid program's exact text that the comment-blanked text has too: Lean's offside rule
    (S has no layout rule), not a comment divergence"""
    fn = f"{D}/lean_{SEED}_{tag}_{r['i']}"
    hdr = "import Nano.V2Self.Prelude\nset_option maxRecDepth 10000\n\n"
    open(fn + ".x.lean", "w").write(hdr + r["src"] + "\n"); open(fn + ".s.lean", "w").write(hdr + strip(r["src"]) + "\n")
    ex, st = parse_errors(lean(fn + ".x.lean")), parse_errors(lean(fn + ".s.lean"))
    pos = lambda es: [e.split(".lean:", 1)[1].split(" error")[0] for e in es]
    return bool(ex) and pos(ex) == pos(st)

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
    if perr and tag.startswith("v"):     # find the programs with a parse error of their own (batches can cascade)
        own = [r for r in items if parse_errors(lean_one(r, tag))]
        return bad + [("LAYOUT" if layout_only(r, tag) else "PARSE", tag, r["i"]) for r in own]
    return bad + [("PARSE", tag, e) for e in perr]

def lean_one(r, tag):
    fn = f"{D}/lean_{SEED}_{tag}_{r['i']}.x.lean"
    open(fn, "w").write("import Nano.V2Self.Prelude\nset_option maxRecDepth 10000\n\n" + r["src"] + "\n")
    return lean(fn)

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
    # a mutant Lean does not accept at all (parse or elaboration error: no #eval value) is a superset acceptance, not a
    # miscompile; everything else (a valid program Lean rejects, or any differing value) is a mismatch
    parse_m = {b[1] for b in bad if b[0] == "PARSE" and b[1].startswith("m")}
    sup = {b[1] for b in bad if b[0] == "mut" and b[3] is None}
    lay = [b for b in bad if b[0] == "LAYOUT"]
    real = [b for b in bad if not (b[0] == "PARSE" and b[1].startswith("m")) and not (b[0] == "mut" and b[3] is None)
            and b[0] != "LAYOUT"]
    print(f"lean: {len(valid)} valid + {len(muts)} accepted mutants, {nchk} runs compared, {skipped} capacity/OOM runs "
          f"skipped; {len(sup | {int(m[1:]) for m in parse_m})} accepted mutants Lean rejects (superset); {len(lay)} valid texts Lean rejects by layout only; {len(real)} mismatches")
    for b in real: print("MISMATCH", str(b)[:300])
    for m in sorted(sup | {int(m[1:]) for m in parse_m}): print("SUPERSET", m)
