#!/usr/bin/env python3
"""scope_check.py SRC OUT (OUT = partition.py output): does any declaration's name resolution differ between SRC (unpartitioned) and OUT?
A declaration elaborates the same in both layouts if every model name it mentions resolves the same way. Every
mentioned name it depended on is imported in OUT (partition.py's closure), so only one thing can differ: a token of x
that names a declaration y visible in OUT but NOT visible at x's original position (y later in the same module, or
in a module that is not an original ancestor). In SRC such a token resolved to something else (a local, an
auto-bound implicit, an opened namespace); in OUT it could resolve to y. Lists every such (x, token) pair.
Also asserts no declaration above V8Base has a dotted name (dot notation could reach it without a matching token)."""
import os, re, sys
OUT_ARG = sys.argv[2]
sys.argv = [sys.argv[0], sys.argv[1], "/nonexistent", "/nonexistent"]
src = sys.argv[1]
OUT_DIR = OUT_ARG
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "partition.py")).read().split("assert \"partial def Reduce__1 \"")[0])
pos = {}
for m in mods:
    for k, (n, _) in enumerate(mods[m][2]): pos[n] = (m, k)
assert not [n for n in names if "." in n], "dotted names above V8Base"
STR = re.compile(r'"(?:\\.|[^"\\])*"')  # string literals hold no identifiers
bad = []
for x in names:
    toks = (tokens(STR.sub('""', text[x])) & names) - {x}
    assert toks <= deps[x]
    mx, kx = pos[x]
    for y in sorted(toks):
        my, ky = pos[y]
        if not ((my == mx and ky < kx) or my in ancestors(mx)): bad.append((x, y))
print(len(bad), "forward tokens")
for x, y in bad: print(x, "->", y)

# The modules below V8Base visible from each core module must be those visible from the original module (else a
# name from Defs etc. could be missing, and in a signature an unknown name can become an auto-bound implicit).
def below(ms):
    seen, todo = set(), list(ms)
    while todo:
        i = todo.pop()
        if i in seen or i not in imp: continue
        seen.add(i); todo += imp[i]
    return {i for i in seen if i not in above}
out = OUT_DIR
cimp = {}
for f in os.listdir(os.path.join(out, "Armv9Core")):
    cimp["Armv9Core." + f[:-5]] = [l.split()[1] for l in open(os.path.join(out, "Armv9Core", f)) if l.startswith("import ")]
def below_out(ms):  # closure in OUT: below modules unchanged, core modules from their files
    seen, todo = set(), list(ms)
    while todo:
        i = todo.pop()
        if i in seen: continue
        seen.add(i); todo += cimp.get(i, imp.get(i, []))
    return {i for i in seen if i in imp and i not in above}
diff = {}
for c in cimp:
    m = "Armv9" if c == "Armv9Core.Root" else "Armv9." + c[len("Armv9Core."):]
    if below([m]) - below_out([c]): diff[c] = below([m]) - below_out([c])
print(len(cimp), "core modules; missing a below-V8Base module:", diff or "none")
assert not diff
