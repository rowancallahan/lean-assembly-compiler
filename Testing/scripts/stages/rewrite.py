#!/usr/bin/env python3
"""Nano/V2Self -> Nano/<stage> rename. usage: rewrite.py map|apply   (run from repo root; called by apply.sh).
Module paths change, def/theorem/namespace names do not. Mapping is rule-based so files added on in-flight branches map too."""
import os, re, subprocess, sys
# (old path relative to Nano/V2Self, new path relative to Nano/); file rules for single files, dir rules per whole segment
FILES = {"C/Lex2": "Lexer/Lex2", "C/Dsg": "Lexer/Dsg", "C/Par1": "Parser/Par1", "C/Own": "Ownership/Own", "C/Gen": "Codegen/Gen", "C/GenArm": "Codegen/GenArm",
         "C/Base": "Main/Chain", "Prelude": "Main/Prelude", "REVIEW": "Main/REVIEW"}
DIRS = {"Proof/Lex": "Lexer", "Proof/Parser": "Parser", "Proof/Own": "Ownership", "Proof/Gen": "Codegen",
        "Proof/Machine": "Run", "Proof/Cert": "SelfHost/Cert", "Proof/CertArm": "SelfHost/CertArm",
        "Proof/SrcLink": "SelfHost/SrcLink", "Proof/Bridge": "SelfHost/Bridge", "Proof/Main": "Main", "Proof/Tests": "Tests"}
STAGES = ["Lexer", "Parser", "Ownership", "Codegen", "Run", "SelfHost", "Main", "Tests"]
def conv(rel):  # rel = path under Nano/V2Self without .lean, '/'-separated; None if unmapped
    if rel in FILES: return FILES[rel]
    seg = rel.split('/')
    for n in range(len(seg), 0, -1):
        d = '/'.join(seg[:n])
        if d in DIRS: return DIRS[d] + ('/' + '/'.join(seg[n:]) if seg[n:] else '')
    return None
TOK = re.compile(r"Nano([./])V2Self(?:[./][A-Za-z0-9_]+(?:[./][A-Za-z0-9_]+)*)")
def sub_tok(m):
    s = m.group(0); sep = m.group(1)
    rel = s[len("Nano.V2Self."):]
    suf = ".lean" if rel.endswith(".lean") else ""
    rel = rel[:len(rel) - len(suf)].replace('.', '/')
    if rel.split('/')[0] in ("Legacy",): return s
    new = conv(rel)
    if new is None: return s
    return "Nano" + sep + new.replace('/', sep) + suf
def tracked(): return subprocess.check_output(["git", "ls-files", "-z"]).decode().split('\0')[:-1]
def moves():
    out = []
    for f in tracked():
        if f.startswith("Nano/V2Self/") and f.endswith(".lean"):
            new = conv(f[len("Nano/V2Self/"):-5])
            assert new, "no rule for " + f
            out.append((f, "Nano/" + new + ".lean"))
    stray = [f for f in tracked() if f.startswith("Nano/V2Self/") and not f.endswith((".lean", "README.md"))]
    assert not stray, "unmapped non-.lean files under Nano/V2Self: " + " ".join(stray)
    news = [n for _, n in out]; assert len(set(news)) == len(news), "target collision"
    return out
SKIP = ("Testing/scripts/stages/", "Legacy/")
# explicit edits for bare `Nano/V2Self` / `Nano.V2Self` uses that are code, not paths: (file, old, new)
ST_FIND = "Nano/Lexer Nano/Parser Nano/Ownership Nano/Codegen Nano/Run Nano/SelfHost Nano/Main Nano/Tests"
ST_GLOBS = ", ".join('"Nano.%s.+"' % s for s in STAGES)
EXPL = [
 ("lakefile.toml", '["Nano.Main.Prelude", "Nano.V2Self.C.+", "Nano.V2Self.Proof.+", "Nano.Main.REVIEW"]', "[" + ST_GLOBS + "]"),
 ("Arm/sail/lakefile.toml", '"Nano.V2Self"', ", ".join('"Nano.%s"' % s for s in STAGES)),
 ("Testing/scripts/deadcode.sh", 'find Nano/V2Self -name', 'find ' + ST_FIND + ' -name'),
 ("Testing/scripts/bigbox/verify.sh", 'find Nano/V2Self -name', 'find ' + ST_FIND + ' -name'),
 ("Testing/scripts/chain434_roots.py", "glob.glob('Nano/V2Self/**/*.lean', recursive=True)",
  "[g for s in %r for g in glob.glob('Nano/%%s/**/*.lean' %% s, recursive=True)]" % STAGES),
 ("Testing/scripts/chain434_roots.py", " and not m.startswith('Nano.V2Self.Legacy.')", ""),
 ("Testing/scripts/deadcode.lean", "(`Nano.V2Self).isPrefixOf mn",
  "([`Nano.Lexer, `Nano.Parser, `Nano.Ownership, `Nano.Codegen, `Nano.Run, `Nano.SelfHost, `Nano.Main, `Nano.Tests].any (·.isPrefixOf mn))"),
]
BARE = re.compile(r"Nano/V2Self(?:/C|/Proof)?(?![A-Za-z0-9_/.])")
EXPL += [
 ("lakefile.toml", "(Nano/V2Self: source C/, proofs Proof/, REVIEW.lean)", "(Nano/{Lexer,Parser,Ownership,Codegen,Run,SelfHost,Main,Tests}: source and proof together per stage, Main/REVIEW.lean)"),
 ("lakefile.toml", "Roots = every Nano/V2Self module", "Roots = every stage-folder module"),
 ("lakefile.toml", "minus Nano/V2Self/Legacy (the old", "(Legacy/ is not a root; the old"),
 ("Testing/nano/v2self/build_self_S.py", 'open(f"Nano/V2Self/C/{p}.lean")',
  'open("Nano/" + {"Base": "Main/Chain", "Lex2": "Lexer/Lex2", "Par1": "Parser/Par1", "Own": "Ownership/Own", "Gen": "Codegen/Gen"}[p] + ".lean")'),
 ("Testing/nano/v2self/ast_dump.lean", "ast.txt Nano/V2Self/Proof 20", "ast.txt Nano/SelfHost 20"),
 ("Nano/Tests/MainCert.lean", "Nano/V2Self/Proof/MainCert", "Nano/Tests/MainCert"),
 ("README.md", "(`Nano/V2Self`, start at `Nano/Main/REVIEW.lean`)", "(`Nano/{Lexer,Parser,Ownership,Codegen,Run,SelfHost,Main,Tests}`, start at `Nano/Main/REVIEW.lean`)"),
 ("README.md", "Nano (Base + V2Self)", "Nano (Base + stage folders)"),
 ("Testing/scripts/review_axioms.sh", "Nano/V2Self/REVIEW.lean", "Nano/Main/REVIEW.lean"),
]
LEG = re.compile(r"(?<!Legacy[./])Nano([./])V2Self(?=[./]Legacy)")
OLD = re.compile(r"(?<!Legacy[./])Nano([./])V2Self(?![A-Za-z0-9_])")
CODE_EXT = (".py", ".sh", ".lean", ".toml")
TOOLS = [
 ("Testing/nano/v2self/gen_cert.py", "Nano.V2Self.Proof.MainCertRules", "Nano.SelfHost.Cert.Rules"),
 ("Testing/nano/v2self/selfcompile.sh", "C=Nano/V2Self/C", "C=Legacy/Nano/V2Self/Legacy/C"),
 ("Testing/nano/v2self/inventory.py", 'f"Nano/V2Self/C/{f}.lean"', 'f"Legacy/Nano/V2Self/Legacy/C/{f}.lean"'),
]
EXPL += TOOLS + [("Nano/Codegen/README.md", "## Files\n* `BufL.lean`", "## Files\n* `Gen.lean`, `GenArm.lean`: the code (RISC-V generator `g41`; native AArch64 back end, prototype with unproven glue).\n* `BufL.lean`")]
def main():
    cmd = sys.argv[1]
    if cmd == "map":
        for a, b in moves(): print(a + "\t" + b)
        return
    assert cmd == "apply"
    # 1. moves (idempotent: nothing left under Nano/V2Self/ after the first run)
    mv = moves()
    for a, b in mv:
        assert os.path.exists(a), "missing " + a
        os.makedirs(os.path.dirname(b), exist_ok=True)
        subprocess.check_call(["git", "mv", a, b])
    newof = {b for _, b in mv}
    # 2. text rewrite of every tracked file
    for f in tracked():
        if f.startswith(SKIP) or not os.path.exists(f) or os.path.islink(f): continue
        try: s = open(f, encoding="utf-8").read()
        except UnicodeDecodeError: continue
        s2 = TOK.sub(sub_tok, s)
        if f in newof: s2 = BARE.sub(os.path.dirname(f), s2)
        for ef, old, new in EXPL:
            if ef == f and old in s2: s2 = s2.replace(old, new)
        if f.endswith(CODE_EXT):  # prose in tools: Nano/V2Self/Legacy -> Legacy/Nano/V2Self/Legacy; any other bare mention -> the stage folders
            s2 = LEG.sub(lambda m: "Legacy" + ("/" if m.group(1) == "/" else ".") + "Nano" + m.group(1) + "V2Self", s2)
            s2 = OLD.sub(lambda m: "Nano" + m.group(1) + "<stages>", s2)
        if s2 != s: open(f, "w", encoding="utf-8").write(s2)
    d = "Testing/scripts/stages/readmes"
    # READMEs already in the tree: old path -> (new path, joins the stage README after the template?)
    RM = {"Proof/Lex": "Lexer", "Proof/Parser": "Parser", "Proof/Own": "Ownership", "Proof/Gen": "Codegen", "Proof/Machine": "Run",
          "Proof/Tests": "Tests", "Proof/Main": "Main", "C": "Main"}
    SUB = {"Proof/Cert": "SelfHost/Cert", "Proof/CertArm": "SelfHost/CertArm", "Proof/SrcLink": "SelfHost/SrcLink", "Proof/Bridge": "SelfHost/Bridge"}
    got = {}
    for od, nd in {**RM, **SUB}.items():
        old = f"Nano/V2Self/{od}/README.md"
        if not os.path.exists(old): continue
        body = TOK.sub(sub_tok, open(old).read())
        for ef, o, n in EXPL:
            if ef == f"Nano/{nd}/README.md": body = body.replace(o, n)
        subprocess.check_call(["git", "rm", "-qf", old])
        if od in SUB: open(f"Nano/{nd}/README.md", "w").write(body)
        else: got.setdefault(nd, []).append(body)
    for st in STAGES:
        tgt = f"Nano/{st}/README.md"; tpl = open(f"{d}/{st}.md").read()
        if st in got:  # main's own README(s) win; the template only fronts the stages that gather several (Main)
            open(tgt, "w").write((tpl + "".join("\n---\n\n" + b for b in got[st])) if st == "Main" else "\n---\n\n".join(got[st]))
        elif not os.path.exists(tgt): open(tgt, "w").write(tpl)
    if not os.path.exists("Nano/README.md") or "V2Self" in open("Nano/README.md").read(): subprocess.check_call(["cp", f"{d}/Nano.md", "Nano/README.md"])
    if os.path.exists("Nano/V2Self/README.md"): subprocess.check_call(["git", "rm", "-qf", "Nano/V2Self/README.md"])
    # 3. asserts: explicit edits all applied; no mapped old path left; no file left in Nano/V2Self except Legacy-free READMEs
    for ef, old, _ in EXPL:
        assert old not in open(ef).read(), "explicit edit not applied: %s: %s" % (ef, old)
    bad = []
    for f in tracked():
        if f.startswith(SKIP) or not os.path.exists(f): continue
        try: s = open(f, encoding="utf-8").read()
        except UnicodeDecodeError: continue
        for m in TOK.finditer(s):
            if sub_tok(m) != m.group(0): bad.append(f + ": " + m.group(0))
    for f in tracked():
        if f.startswith(("Legacy/", "Testing/notes/", "Testing/scripts/stages/")) or not f.endswith(CODE_EXT) or not os.path.exists(f): continue
        for i, l in enumerate(open(f, encoding="utf-8", errors="replace"), 1):
            if OLD.search(l): bad.append(f"{f}:{i}: {l.strip()[:100]}")
    left = [f for f in tracked() if f.startswith("Nano/V2Self/") and f.endswith(".lean")]
    assert not bad and not left, "unrewritten:\n" + "\n".join(bad + left)
main()
