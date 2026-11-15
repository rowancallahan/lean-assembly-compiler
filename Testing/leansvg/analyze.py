#!/usr/bin/env python3
"""Heuristic bottom-up listing of lean-svg's pure functions (import closure of LeanSvg/Render.lean).
usage: analyze.py /path/to/lean-svg  -> defs.json, prints levels and the feature table (not type-checked)"""
import re, sys, os, json, collections
R = sys.argv[1]
def imports(f):
    return [l.split()[1] for l in open(f) if l.startswith("import LeanSvg")]
seen, todo = {}, ["LeanSvg.Render"]
while todo:
    m = todo.pop()
    if m in seen: continue
    f = os.path.join(R, m.replace(".", "/") + ".lean"); seen[m] = f; todo += imports(f)
DEC = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|partial|unsafe|noncomputable)\s+)*(def|abbrev|theorem|instance|structure|inductive|class|opaque)\s+([^\s:({\[]*)")
def strip(s):
    s = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), s, flags=re.S)
    return re.sub(r"--[^\n]*", "", s)
defs = []
for m, f in seen.items():
    src = open(f).read(); lines = strip(src).split("\n"); ns = []
    cur = None
    for n, l in enumerate(lines, 1):
        mm = re.match(r"namespace\s+(\S+)", l)
        if mm: ns.append(mm.group(1)); cur = None; continue
        if re.match(r"end\s+\S+", l) and ns and l.split()[1] == ns[-1].split(".")[-1] or (re.match(r"end\s+(\S+)", l) and ns and l.split()[1] == ns[-1]): ns.pop(); cur = None; continue
        d = DEC.match(l)
        if d or (l and not l[0].isspace() and not l.startswith(("@[", "open", "set_option", "variable", "section", "private", "local", "universe", "attribute", "deriving", "#", "end"))):
            if cur: cur["end"] = n - 1
            cur = None
            if d and d.group(1) in ("def", "abbrev"):
                cur = dict(mod=m, name=".".join(ns + [d.group(2)]), short=d.group(2).split(".")[-1], kind=d.group(1), start=n, end=n, file=f)
                defs.append(cur)
        elif cur: cur["end"] = n
    if cur: cur["end"] = len(lines)
    for dd in defs:
        if dd["mod"] == m and "body" not in dd:
            dd["body"] = "\n".join(lines[dd["start"] - 1:dd["end"]]).rstrip()
            dd["nlines"] = len([x for x in dd["body"].split("\n") if x.strip()])
byshort = collections.defaultdict(list)
for d in defs: byshort[d["short"]].append(d)
def callees(d):
    toks = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", d["body"].split(":=", 1)[1] if ":=" in d["body"] else ""))
    out = set()
    for t in toks:
        for s in {t, t.split(".")[-1]}:
            for e in byshort.get(s, []):
                if e is not d and (e["mod"] == d["mod"] or e["short"] == t or e["name"].endswith(t)): out.add(e["name"])
    return out
byname = {d["name"]: d for d in defs}
for d in defs: d["calls"] = sorted(callees(d))
lvl = {}
def level(n, stack=()):
    if n in lvl: return lvl[n]
    if n in stack: return 99
    c = [level(x, stack + (n,)) for x in byname[n]["calls"] if x in byname]
    lvl[n] = 1 + max(c) if c else 0
    return lvl[n]
for d in defs: d["level"] = level(d["name"])
FEAT = {
 "for/Id.run loop": r"Id\.run|\bfor\b|\bwhile\b", "let mut": r"let mut", "Array": r"\bArray\b|#\[", "push/set": r"\.push\b|\.set|\.modify|\.swap",
 "String/Char": r"\bString\b|\bChar\b|s!\"|toString|\.toList\b", "Int": r"\bInt\b", "Option": r"\bOption\b|\bsome\b|\bnone\b",
 "tuple/structure result": r"×|\{ *[a-z]\w* *:=|\.1\b|\.2\b|⟨", "mul/div/mod": r"[^*]\*[^*]|/ |%|\*\*", "closure/higher-order": r"fun |·|\.map\b|\.foldl|\.any\b|\.all\b|\.filter",
 "HashMap": r"HashMap", "ByteArray": r"ByteArray", "float F32/fix": r"F32|Fx\b", "match/patterns": r"\bmatch\b",
 "UInt32/64": r"UInt32|UInt64", "List": r"\bList\b", "recursion/fuel": r"fuel",
}
for d in defs: d["feat"] = sorted(k for k, r in FEAT.items() if re.search(r, d["body"].split(":=", 1)[-1] if ":=" in d["body"] else d["body"]) or (k in ("ByteArray", "Int", "String/Char", "Array") and re.search(FEAT[k], d["body"].split(":=")[0])))
for d in defs: d.pop("file")
json.dump(defs, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "defs.json"), "w"), indent=0)
print(len(seen), "files", len(defs), "defs")
print("level histogram:", sorted(collections.Counter(min(d["level"], 12) for d in defs).items()))
