#!/usr/bin/env python3
"""Exact-subset evidence (owner's SUBSET RULE): hand-written edge cases + adversarial boundary fuzz through BOTH
`nanoElab` and Lean's REAL frontend (`Testing/nano/oracle.lean`: header-less file = `import Init`, messages with errors =
reject, the entry evaluated by the interpreter).  Verdicts: both reject / nano rejects only (allowed) / both accept with
equal meaning / BUG = nano accepts and Lean rejects, or both accept with different values.
usage: edge.py [N fuzz cases] [seed]   (from the repo root; prints a summary, exit 1 on any BUG)"""
import json, os, random, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", ".."))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 5)
M = 2 ** 64
VALS = [0, 1, 2, 3, M - 1, M - 2, 2 ** 63, 2 ** 63 - 1, 12345678901234567, 7]
def vecs(k): return [[str(rng.choice(VALS)) for _ in range(k)] for _ in range(6)]
import re
def arity(src, name):
    ms = re.findall(r"def\s+" + re.escape(name) + r"((?:\s*\([^)]*\))*)\s*:", src)
    return sum(len(g.split(":")[0].split()) for g in re.findall(r"\(([^)]*)\)", ms[-1])) if ms else 0
def case(src, name="f", ty="UInt64", k=None):
    return dict(src=src, name=name, ty=ty, ins=vecs(arity(src, name)))
H = "def g (a b : UInt64) : UInt64 := a - b\ndef h (a : UInt64) : UInt64 := a * 3\ndef k : UInt64 := 7\n"
def body(e, ty="UInt64", params="x y z"): return H + f"def f ({params} : {ty}) : {ty} := {e}\n"
cases = []
exprs = ["x -1", "x - 1", "x - -1", "x * -1", "-x", "-1", "- 1", "--1", "-(1)", "- -1", "-(-1)", "x--1", "x -y", "x - y - z",
  "x - y * z", "x * y - z", "x - (y - z)", "x + y * z", "(x + y) * z", "x + y + z", "x * y * z", "g x y", "g x y + 1", "g x y * 2",
  "g (x + 1) y", "g x (y)", "g x -1", "g x (-1)", "g -1 x", "g (-1) x", "g x y z", "g x", "g", "h x", "h x + 1", "h x * 2", "h -1", "h (-1)",
  "h x y", "h h x", "h (h x)", "k", "k + 1", "k -1", "k - 1", "k x", "k k", "g k k", "g k -1", "(k) - 1", "h k", "h k + 1",
  "18446744073709551616", "18446744073709551615", "18446744073709551617", "99999999999999999999999999", "0", "00", "007", "1_000", "0x1F", "0b11", "1e3", "1.5", "1.", ".5",
  "x . y", "x.y", "x'", "x 1", "1 x", "1 2", "x y", "(x) (y)", "g(x)(y)", "g (x)(y)", "g x(y)", "h(x)", "(x", "x)", "()", "( )", "((x))",
  "let w := x; w", "let w := x;\n w", "let w := x\n w", "let w := x; w + 1", "let w := x; let v := w; v", "let w := 1; w + let v := 2; v",
  "(let w := 1; w) + 2", "let x := 1; x", "let w := x; let w := w + 1; w", "let w := w; w", "let w := y; x", "let w := x;", "let w := ; x", "let := x; x",
  "let w : UInt64 := x; w", "let w := x in w", "x -- c\n + 1", "x /- c -/ + 1", "x /- c -/", "x + /- c -/ 1", "/- c -/ x", "-- c\n x", "x --c", "x --",
  "x\t+ y", "x +\ty", "x\r\n+ y", "x\r+ y", "x\u00a0+ y", "x\u000b+ y", "x\u000c+ y", "x\u3000+ y", "\ufeffx", "x\n+y", "x\n\n+y",
  "x ;", "x;", "; x", "x + ;", "x +", "+ x", "* x", "x *", "x + + y", "x * * y", "x +* y", "x - - y", "x -- y",
  "fun w => w", "x |>.add y", "x.add y", "x <| y", "y |> x", "if x then y else z", "id x", "max x y", "Nat.add x y", "UInt64.add x y", "x + y |>.toUInt64",
  "(x : UInt64)", "(x : Int64)", "x.toUInt64", "x.val", "x ^ 2", "x / y", "x % y", "x &&& y", "x ||| y", "x <<< y", "x == y", "x :: y",
  "a", "w", "f", "x ∘ y", "x × y", "xx", "x₁", "x_y", "_x", "_", "α", "«x»", "x!", "x?", "g x y .", "g x y,"]
for e in exprs: cases.append(case(body(e)))
for e in exprs: cases.append(case(body(e, "Int64"), ty="Int64"))
# definitions / names / headers
def f1(s, k=1, name="f", ty="UInt64"): cases.append(case(s, name, ty, k))
for nm in ["id", "max", "min", "add", "and", "or", "not", "xor", "ite", "dite", "default", "pure", "bind", "map", "get", "set", "some", "none", "fst", "snd",
           "x", "f2", "fun", "let", "def", "if", "then", "else", "match", "with", "do", "by", "at", "in", "from", "have", "show", "where", "end", "open", "section",
           "namespace", "variable", "theorem", "instance", "structure", "class", "inductive", "mutual", "deriving", "return", "for", "unless", "try", "catch",
           "UInt64", "Int64", "Nat", "Int", "Type", "Prop", "Sort", "sorry", "true", "false", "this", "self", "u", "α", "x'", "x_1", "_x", "_", "a.b", "a1", "A", "Id", "Add", "HAdd", "OfNat", "main", "Inhabited", "Nonempty", "notation", "macro", "syntax", "attribute", "export", "universe", "using", "extends", "private", "protected", "partial", "unsafe", "noncomputable", "abbrev", "example", "opaque", "axiom", "local", "scoped", "termination_by", "decreasing_by", "nomatch", "nofun", "calc", "suffices", "obtain", "assert", "dbgTrace", "panic", "unreachable", "forall", "exists", "fix", "at"]:
    f1(f"def {nm} (x : UInt64) : UInt64 := x + 1\n", name=nm)            # def named nm (entry)
    f1(f"def f ({nm} : UInt64) : UInt64 := {nm} + 1\n")                 # parameter named nm
    f1(f"def g (x : UInt64) : UInt64 := x\ndef f ({nm} : UInt64) : UInt64 := g {nm}\n")
    f1(f"def f (x : UInt64) : UInt64 := let {nm} := x + 1; {nm} * 2\n")  # let named nm
    f1(f"def {nm} (x : UInt64) : UInt64 := x + 1\ndef f (x : UInt64) : UInt64 := {nm} x\n")  # def nm used by a later def
for s in ["", " ", "\n", "-- c\n", "def f (x : UInt64) : UInt64 := x", "def f (x : UInt64) : UInt64 := x\n\n\n", "def f (x : UInt64) : UInt64 := x\n x",
          "def f (x : UInt64) : UInt64 := x\n;", "def f (x : UInt64) : UInt64 := x\n)", "def f (x : UInt64) : UInt64 := x\nx",
          "def f (x : UInt64) : UInt64 := x\ndef f (x : UInt64) : UInt64 := x + 1\n", "def f (x : UInt64) : UInt64 := x\ndef g (x : UInt64) : UInt64 := f x\ndef f (y : UInt64) : UInt64 := g y\n",
          "def f (x : UInt64) : UInt64 := f x\n", "def f (x x : UInt64) : UInt64 := x\n", "def f (x : UInt64) (x : UInt64) : UInt64 := x\n", "def f (x : UInt64) : UInt64 := x\ndef g (y : UInt64) : UInt64 := f y\n",
          "def g (y : UInt64) : UInt64 := f y\ndef f (x : UInt64) : UInt64 := x\n", "def k : UInt64 := 3\ndef f (x : UInt64) : UInt64 := x + k\n", "def k : UInt64 := 3\ndef f (x : UInt64) : UInt64 := k x\n",
          "def f (x : UInt64) : UInt64 := x\ndef f : UInt64 := 1\n", "def f : UInt64 := 1\n", "def f : Int64 := -1\n", "def f : UInt64 := -1\n", "def f (x : UInt64) : Int64 := x\n",
          "def f (x : Int64) : UInt64 := x\n", "def f (x : Int64) : Int64 := x\ndef g (y : UInt64) : UInt64 := y\n", "def g (x : Int64) : Int64 := x\ndef f (y : UInt64) : UInt64 := g y\n",
          "def f(x:UInt64):UInt64:=x\n", "def f (x:UInt64):UInt64:=x+1\n", "def f (x : UInt64) : UInt64 :=\n  x\n", "def f (x : UInt64) : UInt64\n  := x\n", "def f\n(x : UInt64)\n:\nUInt64\n:=\nx\n",
          "def f (x : UInt64) : UInt64 := x\r\n", "def f (x : UInt64)\r\n : UInt64 := x\r\n", "def f (x : UInt64) : UInt64 := x\r", "\tdef f (x : UInt64) : UInt64 := x\n", "def\tf (x : UInt64) : UInt64 := x\n", "def f (x : UInt64) : UInt64 :=\tx\n",
          "def f (x : UInt64) : UInt64 := x\t\n", "\r\ndef f (x : UInt64) : UInt64 := x\n", "\ndef f (x : UInt64) : UInt64 := x", "def f (x : UInt64) : UInt64 := x -- c", "def f (x : UInt64) : UInt64 := x /- c", "def f (x : UInt64) : UInt64 := x /- c -/\n",
          "/- c -/ def f (x : UInt64) : UInt64 := x\n", "-- c\ndef f (x : UInt64) : UInt64 := x\n", "/-- doc -/ def f (x : UInt64) : UInt64 := x\n", "def f (x : UInt64) : UInt64 := /- c -/ x\n", "def /- c -/ f (x : UInt64) : UInt64 := x\n",
          "def f (x y : UInt64) (z : UInt64) : UInt64 := x + y + z\n", "def f (x : UInt64) (y z : UInt64) : UInt64 := x + y + z\n", "def f (x y z : UInt64) : UInt64 := x + y + z\n", "def f (x y z w : UInt64) : UInt64 := x + y + z + w\n",
          "def f () : UInt64 := 1\n", "def f (x : UInt64 ) : UInt64 := x\n", "def f ( x : UInt64) : UInt64 := x\n", "def f {x : UInt64} : UInt64 := x\n", "def f [x : UInt64] : UInt64 := 1\n", "def f (x : UInt64 := 1) : UInt64 := x\n",
          "def f (x : UInt64) : UInt64 := by exact x\n", "def f (x : UInt64) : UInt64 := x where\n", "private def f (x : UInt64) : UInt64 := x\n", "@[inline] def f (x : UInt64) : UInt64 := x\n", "def f (x : UInt64) : UInt64 := x\n#eval f 1\n",
          "theorem t : True := trivial\ndef f (x : UInt64) : UInt64 := x\n", "def f (x : UInt64) : UInt64 := x\ndef f' (y : UInt64) : UInt64 := f y\n", "def f (x : UInt64) : UInt64 := x\n\ndef\n\ng (y : UInt64) : UInt64 := f y\n",
          "def  f  (x : UInt64)  :  UInt64  :=  x\n", "def f (x : UInt64) : UInt64 := x\ndef g (y : UInt64) : UInt64 := let z := f y; z + z\n",
          "def f (x : UInt64) : UInt64 := x\ndef g (y : UInt64) : UInt64 := let z := f y\n z + z\n", "DEF f (x : UInt64) : UInt64 := x\n", "def F (x : UInt64) : UInt64 := x\n", "def f (X : UInt64) : UInt64 := X\n",
          "def f (x : uint64) : uint64 := x\n", "def f (x : UInt64) : UInt64 := x\ndef g (y : UInt64) : UInt64 := h y\n", "def f (x : UInt64) : UInt64 := Nat.succ x\n"]:
    cases.append(case(s, "g" if "def g (y" in s and "def f" in s and s.index("def g (y") > s.index("def f") else "f", "UInt64", 3))
# shadowing of earlier defs by parameters / lets, and uses of the shadowing name as a function
for nm in ["g", "h", "k"]:
    for e in [f"{nm} + 1", f"{nm} 1", f"{nm} x", f"{nm} {nm}", f"{nm} ({nm} + 1)", f"let {nm} := x + 1; {nm} * {nm}", f"let {nm} := x + 1; {nm} {nm}", f"({nm}) - x", f"x - {nm} -1", f"x - {nm} - 1"]:
        for ps in ["x", f"x {nm}", f"{nm} x", f"{nm}"]:
            cases.append(case(H + f"def f ({ps} : UInt64) : UInt64 := {e}\n"))
            cases.append(case(H + f"def f ({ps} : Int64) : Int64 := {e}\n", ty="Int64"))
# every name of Init's root namespace and every identifier-like token of Lean's parser, as def name / parameter / let name; and the nano identifier class
os.makedirs(os.path.join(D, "work"), exist_ok=True)
if not os.path.exists(os.path.join(D, "work", "roots.txt")):
    subprocess.run("PATH=$HOME/.elan/bin:$PATH lake env lean --run Testing/nano/names.lean", shell=True, cwd=ROOT, check=True, capture_output=True)
ROOTS = open(os.path.join(D, "work", "roots.txt")).read().split("\n"); TOKS = open(os.path.join(D, "work", "tokens.txt")).read().split("\n")
assert not [n for n in ROOTS + TOKS if re.fullmatch(r"[a-z][0-9_]*", n)], "an Init name is in nano's identifier class"
import string
MINE = list(string.ascii_lowercase) + [c + s for c in "afgxyz" for s in ["0", "1", "_", "__", "_1", "9_", "10", "_a"]]
for nm in ROOTS + TOKS + MINE:
    f1(f"def {nm} (x : UInt64) : UInt64 := x + 1\n", name=nm)
    f1(f"def f ({nm} : UInt64) : UInt64 := {nm} + 1\n")
    f1(f"def f (x : UInt64) : UInt64 := let {nm} := x + 1; {nm} * 2\n")
    if nm in MINE: f1(f"def {nm} (x : UInt64) : UInt64 := x + 1\ndef f (x : UInt64) : UInt64 := {nm} x * {nm} (x + 2)\n")
# adversarial boundary fuzz: random token soups over a boundary alphabet, and mutations of valid programs
ALPHA = ["x", "y", "z", "g", "h", "k", "f", "1", "2", "0", "18446744073709551616", "(", ")", "+", "-", "*", ";", "let", "w", ":=", "w", " ", " ", "\n", "\t", "\r", "--", "/-", "-/", "id", "max", "add", "x'", "_", ".", "fun", "=>", ":", "UInt64", "def"]
def soup(n): return "".join(rng.choice(ALPHA) + rng.choice(["", " ", " ", "\n"]) for _ in range(n))
for _ in range(N): cases.append(case(body(soup(rng.randint(1, 8)), rng.choice(["UInt64", "Int64"])), ty="UInt64"))
GOOD = ["x + y * z", "g x y - z", "h x + k", "let w := x + 1; w * y", "(x - y) - z", "x - -1", "g (x + 1) (y * 2)", "h (h x) + g y z", "let w := g x y; let v := h w; v - z", "k * k - x", "-1 + x", "x * (-3)", "- 1 - x"]
TOK = ["x", "y", "z", "g", "h", "k", "1", "-1", "(", ")", "+", "-", "*", ";", "let w :=", "w", "--", "id", "x'", "\n", "\t", " "]
def mutate(e):
    ts = e.split(" ")
    for _ in range(rng.randint(1, 3)):
        i = rng.randrange(len(ts) + 1); op = rng.randrange(4)
        if op == 0 and ts: del ts[min(i, len(ts) - 1)]
        elif op == 1: ts.insert(i, rng.choice(TOK))
        elif op == 2 and ts: ts[min(i, len(ts) - 1)] = rng.choice(TOK)
        elif ts: j = rng.randrange(len(ts)); ts[min(i, len(ts) - 1)], ts[j] = ts[j], ts[min(i, len(ts) - 1)]
    return " ".join(ts)
for _ in range(N): cases.append(case(body(mutate(rng.choice(GOOD)), rng.choice(["UInt64", "Int64"])), ty="UInt64"))
# layout fuzz: valid programs with random separators (including none, newlines at column 0, trailing spaces) between tokens
import re as _re
SEPS = [" ", " ", " ", "\n", "\n ", " \n", "\n\n", "  ", "", "\n  ", "\r\n", "\t"]
def toks(t): return _re.findall(r"[A-Za-z0-9_]+|:=|[-+*();:]", t)
PROGS = [H + "def f (x y z : UInt64) : UInt64 := " + e + "\n" for e in GOOD] + [
  "def g (x y : UInt64) : UInt64 := x - y\ndef f (x : UInt64) : UInt64 := let w := g x 5; let v := g w w; v - w * x\n",
  "def k : UInt64 := 3\ndef f (x : UInt64) : UInt64 := k * k - (x + k) * -2\n", "def f (x y : UInt64) : UInt64 := (x) - (y)\n"]
for _ in range(N):
    p = rng.choice(PROGS); ts = toks(p)
    out, sp = "", None
    for i, t in enumerate(ts):
        sep = rng.choice(SEPS) if rng.random() < 0.5 else rng.choice(SEPS[:7])
        if sep == "" and i + 1 < len(ts) and re.match(r"\w", t[-1]) and re.match(r"\w", ts[i + 1][0]): sep = " "
        out += t + sep
    cases.append(case(out, name="f", ty="UInt64"))
# types: the oracle needs the entry's type to wrap Int64 arguments
for c in cases:
    if "def f (x y z : Int64) : Int64" in c["src"] or "(x : Int64) : Int64" in c["src"] or "def f : Int64" in c["src"]: c["ty"] = "Int64"
    c["name"] = c["name"]
inp = "\n".join(json.dumps(c) for c in cases) + "\n"
out = subprocess.run("PATH=$HOME/.elan/bin:$PATH lake env lean --run Testing/nano/oracle.lean", shell=True, cwd=ROOT, input=inp, capture_output=True, text=True)
if out.returncode: print(out.stderr[-2000:]); sys.exit(2)
lines = out.stdout.splitlines(); assert len(lines) == len(cases), (len(lines), len(cases))
stat = dict(both_reject=0, nano_only_rejects=0, both_accept_equal=0, both_accept_unevaluated=0, BUG_nano_accepts_lean_rejects=0, BUG_meanings_differ=0)
bugs = []; uneval = []
for c, l in zip(cases, lines):
    r, n = l.split(" nano=")
    r = r[len("real="):]
    if r == "R" and n == "R": stat["both_reject"] += 1
    elif r != "R" and n == "R": stat["nano_only_rejects"] += 1
    elif r == "R": stat["BUG_nano_accepts_lean_rejects"] += 1; bugs.append((c["src"], l))
    elif "?" in r: stat["both_accept_unevaluated"] += 1; uneval.append(c["src"])
    elif r == n: stat["both_accept_equal"] += 1
    else: stat["BUG_meanings_differ"] += 1; bugs.append((c["src"], l))
print(len(cases), "cases:", stat)
for u in uneval[:5]: print("UNEVAL", repr(u))
seen = set()
for s, l in bugs:
    if s in seen: continue
    seen.add(s); print("BUG", repr(s), l)
sys.exit(1 if bugs else 0)
