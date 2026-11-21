#!/usr/bin/env python3
"""fuzz_syntax.py: differential fuzz of the syntax extensions (SYNTAX_EXP.md): trivia (comments, docstrings, attributes,
namespace/section/open/end, private) and `match`.  UNPROVEN test glue.
Each case is a random program, generated as an AST and rendered twice:
  NEW = with `match` and random trivia (what the new compiler must accept), compiled by the NEW B2 / NEW native-ARM compiler;
  OLD = trivia stripped, `match` desugared by hand exactly as DsSpec.ds does, compiled by MAIN's B2 / native-ARM compiler.
Checks (a) code bytes NEW == OLD (RISC-V and A64) and run outputs RISC-V == A64 on random inputs (QEMU);
(b) the outputs equal Lean's own `#eval` of NEW; (c) mutants (token edits, broken comments/attributes, missing or
redundant match arms): if the new compiler accepts one, Lean must accept it with the same outputs (never miscompiled).
usage: fuzz_syntax.py DIR SEED N_VALID N_MUTANT   (DIR holds B2_new.bin B2_main.bin GA_new.bin GA_main.bin shim_rv shim_arm)"""
import os, random, subprocess, sys, json
from multiprocessing import Pool

D, SEED, NV, NM = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../../.."))
LITS = [0, 1, 2, 3, 5, 7, 10, 48, 57, 65, 97, 255, 256, 1000, 18446744073709551615]
OPS = ["+", "-", "*", "&&&", "|||", "<<<", ">>>"]

# ---------------- AST: ("lit",n) ("var",v) ("bin",op,a,b) ("if",cmp,a,b,t,e) ("let",v,val,body) ("call",f,[args])
#                       ("match",scrut,arms,catch) arms=[(lit,body)] catch=("wild",body)|("var",v,body)
#                       ("pmatch",e1,e2,p,q,body)
class G:
    def __init__(s, rng): s.r = rng; s.n = 0
    def pin(s, e, vs):
        return e if typed(e) else ("bin", "+", e, ("bin", "*", ("var", vs[0]), ("lit", 0)))
    def fresh(s, p="v"): s.n += 1; return f"{p}{s.n}"
    def expr(s, d, vs, defs, nm=False):
        """nm: no match inside (a scrutinee may not contain `match`, DsSpec.go)"""
        r = s.r; k = r.random()
        if nm and k >= 0.68: k = 0.3
        if d <= 0 or k < 0.18:
            return ("var", r.choice(vs)) if vs and r.random() < 0.6 else ("lit", r.choice(LITS))
        if k < 0.38:
            op, a, b = r.choice(OPS), s.expr(d - 1, vs, defs, nm), s.expr(d - 1, vs, defs, nm)
            if op in ("<<<", ">>>"): b = ("lit", r.randrange(64))  # S shifts by literal amounts only
            if op in ("<<<", ">>>", "&&&", "|||") and not typed(a) and not typed(b): a = s.pin(a, vs)  # Lean: no Nat default
            return ("bin", op, a, b)
        if k < 0.50: return ("if", r.choice(["==", "<"]), s.pin(s.expr(d - 1, vs, defs, nm), vs), s.pin(s.expr(d - 1, vs, defs, nm), vs),
                             s.expr(d - 1, vs, defs, nm), s.expr(d - 1, vs, defs, nm))
        if k < 0.60:
            v = s.fresh(); return ("let", v, s.pin(s.expr(d - 1, vs, defs, nm), vs), s.expr(d - 1, vs + [v], defs, nm))
        if k < 0.68 and defs:
            f, ar = r.choice(defs); return ("call", f, [s.expr(d - 2, vs, defs, nm) for _ in range(ar)])
        if nm: return ("bin", "+", s.expr(d - 1, vs, defs, nm), s.expr(d - 1, vs, defs, nm))
        if k < 0.75:
            p, q = s.fresh("p"), s.fresh("q")
            return ("pmatch", s.pin(s.expr(d - 1, vs, defs, True), vs), s.pin(s.expr(d - 1, vs, defs, True), vs), p, q, s.expr(d - 1, vs + [p, q], defs))
        lits = r.sample(LITS[:12], r.randint(0, 4))
        arms = [(l, s.expr(d - 1, vs, defs, nm)) for l in lits]
        if r.random() < 0.5: c = ("wild", s.expr(d - 1, vs, defs, nm))
        else:
            v = s.fresh("w"); c = ("var", v, s.expr(d - 1, vs + [v], defs, nm))
        return ("match", s.pin(s.expr(d - 1, vs, defs, True), vs), arms, c)

def simple(e): return e[0] in ("lit", "var", "bin", "call")

def typed(e):
    """Lean infers UInt64 for e without an expected type (a literal-only term would default to Nat)"""
    t = e[0]
    if t in ("var", "call"): return True
    if t == "bin":
        if e[1] in ("<<<", ">>>"): return typed(e[2])
        return typed(e[2]) or typed(e[3])
    if t == "if": return typed(e[4]) or typed(e[5])
    if t == "let": return typed(e[3])
    if t == "match": return any(typed(b) for _, b in e[2]) or typed(e[3][1] if e[3][0] == "wild" else e[3][2])
    if t == "pmatch": return typed(e[5])
    return False

# ---------------- rendering to tokens.  tail: the expression may extend to the end of its context
ASC = [False]   # Lean copy only: ascribe `( e : UInt64 )` where Lean has no expected type (never shown to the compilers)
def A(toks): return ["(", "("] + toks + [")", ":", "UInt64", ")"] if ASC[0] else toks
def rn(e, new, tail, cnt):
    t = e[0]
    if t == "lit": return [str(e[1])]
    if t == "var": return [e[1]]
    if t == "bin": return ["("] + A(rn(e[2], new, False, cnt)) + [e[1]] + A(rn(e[3], new, False, cnt)) + [")"]
    if t == "if":
        return ["(", "if"] + A(rn(e[2], new, False, cnt)) + [e[1]] + A(rn(e[3], new, False, cnt)) + ["then"] + \
               rn(e[4], new, True, cnt) + ["else"] + rn(e[5], new, True, cnt) + [")"]
    if t == "let": return ["(", "let", e[1], ":="] + A(rn(e[2], new, True, cnt)) + [";"] + rn(e[3], new, True, cnt) + [")"]
    if t == "call":
        out = ["(", e[1]]
        for a in e[2]: out += rn(a, new, False, cnt)
        return out + [")"]
    if t == "pmatch":
        pair = ["("] + A(rn(e[1], new, False, cnt)) + [","] + A(rn(e[2], new, False, cnt)) + [")"]
        if new:
            body = ["match"] + pair + ["with", "|", "(", e[3], ",", e[4], ")", "=>"] + rn(e[5], new, True, cnt)
            if ASC[0]: return A(body)
            return body if tail and simple(e[5]) else ["("] + body + [")"]
        cnt[0] += 1; z = f"zq{cnt[0]}"
        return ["(", "let", z, ":="] + pair + [";", "let", "(", e[3], ",", e[4], ")", ":=", z, ";"] + rn(e[5], new, True, cnt) + [")"]
    if t == "match":
        _, sc, arms, c = e
        cbody = c[1] if c[0] == "wild" else c[2]
        if new:
            out = ["match"] + A(rn(sc, new, False, cnt)) + ["with"]
            for l, b in arms: out += ["|", str(l), "=>"] + rn(b, new, False, cnt)
            out += ["|", "_" if c[0] == "wild" else c[1], "=>"] + rn(cbody, new, True, cnt)
            if ASC[0]: return A(out)
            return out if tail and simple(cbody) else ["("] + out + [")"]
        cnt[0] += 1; z = f"zq{cnt[0]}"
        out = ["(", "let", z, ":="] + rn(sc, new, False, cnt) + [";"]
        for i, (l, b) in enumerate(arms):
            out += (["else"] if i else []) + ["if", z, "==", str(l), "then"] + rn(b, new, False, cnt)
        out += ["else"] if arms else []
        if c[0] == "var": out += ["let", c[1], ":=", z, ";"]
        return out + rn(cbody, new, True, cnt) + [")"]

def program(rng):
    g = G(rng); defs = []; out = []
    for i in range(rng.randint(1, 4)):
        ar = rng.choice([1, 2]); ps = ["a", "b"][:ar]; name = f"g{i}"
        body = g.expr(rng.randint(1, 5), ps, defs)
        out.append((name, ps, body)); defs.append((name, ar))
    # the byte function: h (c i : UInt64), using the helpers
    hb = g.expr(rng.randint(2, 5), ["c", "i"], defs)
    out.append(("h", ["c", "i"], hb))
    return out

LOOP = ["def", "f", ":", "Nat", "→", "List", "UInt8", "→", "UInt64", "→", "List", "UInt8", "→", "List", "UInt8", "\n",
        "|", "0", ",", "x", ",", "i", ",", "o", "=>", "o", "\n",
        "|", "n", "+", "1", ",", "x", ",", "i", ",", "o", "=>", "f", "n", "x", "(", "i", "+", "1", ")",
        "(", "put", "o", "(", "h", "(", "rd", "x", "i", ")", "i", ")", ")", "\n",
        "def", "m", "(", "x", ":", "List", "UInt8", ")", ":", "List", "UInt8", ":=", "f", "(", "len'", "x", ")", "x", "0", "[", "]", "\n"]

def deftoks(name, ps, body, new):
    return ["def", name, "("] + ps + [":", "UInt64", ")", ":", "UInt64", ":="] + rn(body, new, True, [0]) + ["\n"]

WORDS = ["match", "with", "|", "=>", "def", "let", "end", "open", "x", "if", "(", ")", "--", "@[", "]", "_", "λ", "é", "0"]
def bcomment(rng, d=0):
    parts = [rng.choice(WORDS) for _ in range(rng.randint(0, 4))]
    if d < 2 and rng.random() < 0.3: parts.insert(rng.randint(0, len(parts)), bcomment(rng, d + 1))
    return "/- " + " ".join(parts) + " -/"
def trivia(rng):
    k = rng.random()
    if k < 0.35: return "-- " + " ".join(rng.choice(WORDS + ["/-", "-/"]) for _ in range(rng.randint(0, 4))) + "\n"
    if k < 0.75: return bcomment(rng)
    return "\n"

def render_new(rng, prog, ns, rate):
    """text of NEW: def-level trivia + token-level trivia"""
    lines = [f"/-! fuzz program -/", f"namespace {ns}", "open Nat"]
    sec = rng.random() < 0.5
    if sec: lines.append("section S")
    for name, ps, body in prog:
        mods = []
        if rng.random() < 0.3:   # docstrings; Lean skips whitespace, `--` lines and plain block comments after the opener
            w = rng.choice([x for x in WORDS if "-" not in x and "/" not in x])
            mods.append(rng.choice(["/-- " + w + " -/", "/-- -- " + w + " -/\n " + w + " -/", "/-- /- " + w + " -/ -- -/\n -/",
                                    "/--\n -- " + w + "\n " + w + " /- " + w + " -/ -/", "/---/", "/-- " + w + " -- -/"]))
        if rng.random() < 0.3: mods.append(rng.choice(["@[inline]", "@[reducible]", "@[inline, reducible]"]))
        if rng.random() < 0.3: mods.append("private")
        toks = deftoks(name, ps, body, True)
        s = []; inarm = 0
        for tk in toks:
            s.append(tk)
            if tk == "|": inarm = 1
            elif inarm == 1 and tk == "=>": inarm = 2
            elif inarm == 2: inarm = 0
            if tk != "\n" and rng.random() < rate:
                tv = trivia(rng)
                s.append(bcomment(rng) if inarm and (tv.endswith("\n")) else tv)
        # Lean's offside rule: after a line break, indent past every `match` / `|` column seen so far in the def
        txt, col, hi = "", 0, 0
        for piece in s:
            if txt and not txt.endswith("\n"): txt += " "; col += 1
            if piece in ("match", "|"): hi = max(hi, col)
            txt += piece
            col = len(txt) - txt.rfind("\n") - 1 if "\n" in piece else col + len(piece)
            if txt.endswith("\n") and piece != "\n" or piece == "\n":
                pass
            if txt.endswith("\n"):
                txt += " " * (hi + 2); col = hi + 2
        lines.append(" ".join(mods) + ("\n" if mods and rng.random() < 0.5 else " ") + txt)
    if sec: lines.append("end S")
    lines.append(" ".join(LOOP))
    lines.append(f"end {ns}")
    return "\n".join(lines) + "\n"

def render_lean(prog, ns):
    """the Lean copy of NEW for #eval: the same program without trivia, with type ascriptions"""
    ASC[0] = True
    try: body = "\n".join(" ".join(deftoks(n, p, b, True)) for n, p, b in prog)
    finally: ASC[0] = False
    return f"namespace {ns}L\n{body}\n" + " ".join(LOOP) + f"\nend {ns}L\n"

def render_old(prog):
    return "\n".join(" ".join(deftoks(n, p, b, False)) for n, p, b in prog) + "\n" + " ".join(LOOP) + "\n"

# ---------------- running
def q(args, inp):
    p = subprocess.run(args, input=inp, capture_output=True, timeout=120)
    return p.stdout, p.stderr.decode(errors="replace").strip().split("\n")[-1]
def comp(compiler, arm, src):
    sh = f"{D}/shim_arm" if arm else f"{D}/shim_rv"
    return q(["qemu-aarch64" if arm else "qemu-riscv64", sh, f"{D}/{compiler}"], src.encode())[0]
def run(code, arm, inp, tmp):
    fn = f"{tmp}.{'a' if arm else 'r'}.bin"; open(fn, "wb").write(code)
    sh = f"{D}/shim_arm" if arm else f"{D}/shim_rv"
    out, st = q(["qemu-aarch64" if arm else "qemu-riscv64", sh, fn], inp)
    return out, st.split(":", 1)[-1].strip()

def inputs(rng): return [b"", bytes(rng.randrange(256) for _ in range(5)), bytes(rng.randrange(256) for _ in range(40))]

def case_valid(i):
    rng = random.Random(SEED * 1000003 + i)
    prog = program(rng); ns = f"Fz{i}"
    new = render_new(rng, prog, ns, rng.choice([0.0, 0.1, 0.3])); old = render_old(prog)
    tmp = f"{D}/w/v{i}"
    rn_, ro = comp("B2_new.bin", False, new), comp("B2_main.bin", False, old)
    an, ao = comp("GA_new.bin", True, new), comp("GA_main.bin", True, old)
    r = {"i": i, "kind": "valid", "ns": ns, "src": new, "lsrc": render_lean(prog, ns)}
    if not ro: r["res"] = "old-rejects"; return r          # generator produced something the old compiler rejects
    if not rn_: r["res"] = "MISMATCH new-rejects"; return r
    if rn_ != ro: r["res"] = "MISMATCH rv-code"; return r
    if an != ao: r["res"] = "MISMATCH a64-code"; return r
    outs = []
    for inp in inputs(rng):
        o1, s1 = run(rn_, False, inp, tmp); o2, s2 = run(an, True, inp, tmp)
        if (o1, s1) != (o2, s2): r["res"] = f"MISMATCH rv-vs-a64 {s1} {s2}"; return r
        outs.append([list(inp), s1, list(o1)])
    r["res"] = "ok"; r["outs"] = outs; return r

def mutate(rng, prog, ns):
    k = rng.random()
    if k < 0.15:
        return render_new(rng, prog, ns, 0.1) + rng.choice(["/- unterminated", "/- a /- b -/", "@[inline", "-/"]), "nolean"
    if k < 0.27:   # Lean-quirk trivia (doc openers, `open … in`, attribute contents) before a def or inside a body
        text = render_new(rng, prog, ns, 0.1).split("\n")
        idx = [j for j, l in enumerate(text) if l.startswith(("def g", "def h", "/--", "@[", "private"))]
        if idx:
            j = rng.choice(idx)
            if rng.random() < 0.3 and ":=" in text[j]:
                text[j] = text[j].replace(":=", rng.choice([":= open Nat in", ":= open Nat in\n", ":= open Nat\n in"]), 1)
            else:
                text.insert(j, rng.choice(["/-- -- x -/", "/-- -- x -/\n y -/", "/-- --/", "/--/ x -/", "/-! /- a -/ -- b -/\n c -/",
                    "/-- /--/ -/ -/", "/-- /-! q -/ -/", "/- /-- x -/ -/", "open Nat in", "open Nat -- c", "open Nat.Foo",
                    "namespace A.B", "@[inline -- ]\n]", "@[x.y]", "@[simp, inline]", "@[ inline ]", "/-- \r\n-- x -/\n y -/"]))
        return "\n".join(text), "lean"
    if k < 0.35:   # break a match: drop the catch-all arm or add an arm after it (re-render from the AST)
        def walk(e):
            if e[0] == "match":
                return ("bad", e[1], e[2], e[3]) if rng.random() < 0.5 else e
            return e
        def dropc(e):
            if isinstance(e, tuple):
                if e[0] == "match" and rng.random() < 0.6:
                    if rng.random() < 0.5: return ("matchnc", dropc(e[1]), [(l, dropc(b)) for l, b in e[2]])
                    return ("matchx", dropc(e[1]), [(l, dropc(b)) for l, b in e[2]], e[3])
                return tuple(dropc(x) if isinstance(x, tuple) else ([dropc(y) if isinstance(y, tuple) else y for y in x] if isinstance(x, list) else x) for x in e)
            return e
        prog2 = [(n, p, dropc(b)) for n, p, b in prog]
        return render_new(rng, prog2, ns, 0.1), "lean"
    # token-level: edit one token of one def body (namespace lines untouched)
    text = render_new(rng, prog, ns, 0.0).split("\n")
    idx = [j for j, l in enumerate(text) if l.lstrip().startswith(("def g", "def h", "private", "@[", "/--")) and ":=" in l]
    if not idx: return "\n".join(text), "lean"
    j = rng.choice(idx); toks = text[j].split(" ")
    p = rng.randrange(len(toks)); m = rng.random()
    if m < 0.3: del toks[p]
    elif m < 0.5: toks.insert(p, toks[p])
    elif m < 0.7 and p + 1 < len(toks): toks[p], toks[p + 1] = toks[p + 1], toks[p]
    else: toks.insert(p, rng.choice(["match", "with", "|", "=>", "_", "(", ")", "3", ",", "end", "x", "@[x]"]))
    text[j] = " ".join(toks)
    return "\n".join(text), "lean"

# extra renderings used only by mutants
_rn = rn
def rn(e, new, tail, cnt):
    if e[0] in ("matchnc", "matchx"):
        out = ["(", "match"] + rn(e[1], new, False, cnt) + ["with"]
        for l, b in e[2]: out += ["|", str(l), "=>"] + rn(b, new, False, cnt)
        if e[0] == "matchx":
            c = e[3]; cb = c[1] if c[0] == "wild" else c[2]
            out += ["|", "_" if c[0] == "wild" else c[1], "=>"] + rn(cb, new, False, cnt) + ["|", "3", "=>", "0"]
        return out + [")"]
    return _rn(e, new, tail, cnt)

def case_mut(i):
    rng = random.Random(SEED * 7919 + i + 10 ** 9)
    prog = program(rng); ns = f"Mu{i}"
    src, mode = mutate(rng, prog, ns)
    rn_ = comp("B2_new.bin", False, src)
    r = {"i": i, "kind": "mut", "ns": ns, "src": src, "mode": mode}
    if not rn_: r["res"] = "rejected"; return r
    if mode == "nolean": r["res"] = "MISMATCH accepted-broken-trivia"; return r
    an = comp("GA_new.bin", True, src); tmp = f"{D}/w/m{i}"
    if not an: r["res"] = "MISMATCH a64-rejects"; return r
    outs = []
    for inp in inputs(rng):
        o1, s1 = run(rn_, False, inp, tmp); o2, s2 = run(an, True, inp, tmp)
        if (o1, s1) != (o2, s2): r["res"] = "MISMATCH rv-vs-a64"; return r
        outs.append([list(inp), s1, list(o1)])
    r["res"] = "accepted"; r["outs"] = outs; return r

if __name__ == "__main__":
    os.makedirs(f"{D}/w", exist_ok=True)
    with Pool(int(os.environ.get("JOBS", "4"))) as pool:
        res = pool.map(case_valid, range(NV), chunksize=8) + pool.map(case_mut, range(NM), chunksize=8)
    json.dump(res, open(f"{D}/res_{SEED}.json", "w"))
    from collections import Counter
    print(Counter(r["res"].split(" ")[0] if r["res"].startswith("MISMATCH") else r["res"] for r in res))
    for r in res:
        if r["res"].startswith("MISMATCH"): print(r["i"], r["kind"], r["res"]); print(r["src"][:600]); break
