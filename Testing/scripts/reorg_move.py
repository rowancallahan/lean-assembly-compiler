#!/usr/bin/env python3
"""Nano/<stages> reorganization (NANO_V2_REORG.md): move every proof module into Proof/{Lex,Parser,Own,Gen,Machine,Bridge,
Cert,SrcLink,Main,Tests}/ and rewrite every reference to the old module names / paths.  No proof text changes.
usage: reorg_move.py --dry   (print the mapping and the files that would change)
       reorg_move.py --go    (git mv + rewrite; run from the repo root on a clean tree)
Fails (assert) on any proof module it cannot classify, so new modules must be added to the rules first."""
import os, re, subprocess, sys

DRY = "--dry" in sys.argv
assert DRY or "--go" in sys.argv, __doc__
P = "Nano/<stages>/Proof"

# modules left in place: outside REVIEW's closure / dead, pending the owner's deletion decision (NANO_V2_DEADCODE.md)
STAY = {"MainCert", "MainCertRules", "MainPure", "ParInvGlue", "ParLet"} | {f"MainCertC{i}" for i in range(10)}
TESTS = {"OwnNV", "MainWitness"}
RULES = [
    ("Lex", r"(MainTokWF|ParTokWF)"),
    ("Parser", r"(Par(Spec|SpecLen|SpecTail|Rep|TreeOK|SerLen|CapBnd|Run.*|Inv.*)|MainTyP|DBPar)"),
    ("Own", r"(Own(Spec|WF|Stage|P\d+)|MainKeep)"),
    ("Gen", r"(Gen(Ref|Top|Width|All)|Fixup|BufL|DBNode)"),
    ("Bridge", r"(MainBridge\d*|MainConv.*|MainShift\d*|MainTy|MainOk|SemX)"),
    ("Main", r"(Main|MainTop|MainTopE|DBStageE|GenStageE|SelfLink|SelfC|RunsTop)"),
    ("SrcLink", r"SrcLink"),
    ("Machine", r"(Call|CallA|CallExact|Expr|ExprExact|ExprBridge|ExprEV|Templates|TmGood|Heap|HeapEV|Loop|SimW|SimX|SimXB|"
                r"Bridge|MachExact|Nd.*|NoW|EV.*|SafeRun|RoomRun|Cap.*|Start.*|GenRun|GenRunS|Host.*|GenImpl|GenMain|Runs(Shift|Thr|Def))"),
]

def cls(b):
    if b in STAY: return None
    if b in TESTS or re.search(r"NV|Witness|^Audit", b): return "Tests"
    hits = [c for c, r in RULES if re.fullmatch(r, b)]
    assert len(hits) == 1, f"cannot classify {b}: {hits}"
    return hits[0]

def mod(path): return path[:-5].replace("/", ".")

moves = {}  # old path -> new path
for f in sorted(os.listdir(P)):
    if f.endswith(".lean"):
        c = cls(f[:-5])
        if c: moves[f"{P}/{f}"] = f"{P}/{c}/{f}"
for f in sorted(os.listdir(f"{P}/Src")):
    assert f.endswith(".lean"), f
    moves[f"{P}/Src/{f}"] = f"{P}/SrcLink/{f}"
for f in ("Lex2Spec", "Lex2Sound"):
    moves[f"Nano/<stages>/C/{f}.lean"] = f"{P}/Lex/{f}.lean"
# Cert stays where it is (Proof/Cert)
modmap = {mod(o): mod(n) for o, n in moves.items()}
pathmap = dict(moves)
# collisions: two modules may not land on one path, and no new path may equal an old, unmoved module
assert len(set(moves.values())) == len(moves)
for n in moves.values(): assert n not in moves or moves[n] != n

TOK = re.compile(r"Nano[./]V2Self[./][A-Za-z0-9_./]*[A-Za-z0-9_]")
def rewrite(s):
    def sub(m):
        t = m.group(0)
        if "/" in t:  # a path: longest mapped prefix "X.lean" or a directory
            for o, n in pathmap.items():
                if t == o or t == o[:-5]: return n if t == o else n[:-5]
            return t
        # a module name, possibly with a suffix after it (e.g. `Nano.<stages>.Proof.Src.Data{g}` in generators)
        if t in modmap: return modmap[t]
        return t
    s2 = TOK.sub(sub, s)
    # generator prefixes: srclink/gen.lean prints `Nano.<stages>.Proof.Src.<X>{g}` and writes into Proof/Src/
    s2 = s2.replace("Nano.<stages>.Proof.Src.", "Nano.SelfHost.SrcLink.").replace("Nano/<stages>/Proof/Src/", "Nano/SelfHost/SrcLink/")
    s2 = s2.replace('"Nano/<stages>/Proof/Src"', '"Nano/SelfHost/SrcLink"')
    return s2

files = subprocess.run(["git", "ls-files", "*.lean", "*.py", "*.sh", "*.md", "*.toml", "*.txt"], capture_output=True,
                       text=True, check=True).stdout.split()
changed = []
for f in files:
    if not os.path.isfile(f) or f.startswith(".lake"): continue
    if f in ("Testing/notes/NANO_V2_REORG.md", "Testing/notes/NANO_V2_DEADCODE.md", "Testing/scripts/reorg_move.py"): continue  # old names on purpose
    try: s = open(f, encoding="utf-8").read()
    except UnicodeDecodeError: continue
    s2 = rewrite(s)
    if s2 != s: changed.append((f, s2))

if DRY:
    for o, n in moves.items(): print("MOVE", o, "->", n)
    for f, _ in changed: print("EDIT", f)
    print(f"{len(moves)} moves, {len(changed)} files edited")
    sys.exit(0)

for f, s2 in changed: open(f, "w", encoding="utf-8").write(s2)
for o, n in moves.items():
    os.makedirs(os.path.dirname(n), exist_ok=True)
    subprocess.run(["git", "mv", o, n], check=True)
print(f"{len(moves)} moves, {len(changed)} files edited")
