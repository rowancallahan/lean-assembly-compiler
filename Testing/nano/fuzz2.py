"""nano v2 increment 1 (`if` + `==`/`<`/`<=`): subset check of `Nano.V2.nanoElab` against Lean's REAL frontend
(Testing/nano/oracle2.lean).  Cases: hand-written boundary cases (lexing of the comparison tokens, precedence, layout,
the typing guard, signed vs unsigned, nesting) as UInt64 and Int64, the v1 corpus (v2 must accept it unchanged), random
programs with `if` nodes, token mutations.  Verdict per case: both reject / nano only rejects (allowed) / equal / BUG.
usage: python3 Testing/nano/fuzz2.py N seed      (exit 1 on any BUG)"""
import json, os, random, re, subprocess, sys
sys.path.insert(0, os.path.dirname(__file__))
from nanolib import CORPUS, INT_CORPUS, M, entry_arity
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
EDGE = [0, 1, 2, 3, 7, 255, 2**32, 2**63 - 1, 2**63, 2**63 + 1, M - 2, M - 1]

def ins(k, n=8):
    return [[str(rng.choice(EDGE) if rng.random() < .6 else rng.randrange(M)) for _ in range(k)] for _ in range(n)]

def case(src, ty="UInt64"):
    try: k = entry_arity(src)
    except Exception: k = 2
    return dict(src=src, name=(re.findall(r"^def\s+(\w+)", src, re.M) or ["f"])[-1], ty=ty, ins=ins(k))

H2 = "def f (x y : T) : T := "
BODIES = [
 "if x < y then 1 else 2", "if x <= y then 1 else 2", "if x == y then 1 else 2",
 "if x<y then 1 else 2", "if x <y then 1 else 2", "if x< y then 1 else 2", "if x<=y then 1 else 2", "if x =< y then 1 else 2",
 "if x < -1 then 1 else 2", "if -1 < x then 1 else 2", "if x == -1 then 1 else 2", "if x === y then 1 else 2",
 "if x != y then 1 else 2", "if x >= y then 1 else 2", "if x > y then 1 else 2", "if x = y then 1 else 2",
 "if x <- y then 1 else 2", "if x <<< y then 1 else 2", "if x == y == x then 1 else 2", "if x < y < x then 1 else 2",
 "if x < y then 1", "if x < y else 2", "if then 1 else 2", "if x then 1 else 2", "if x < y then else 2",
 "if x + 1 < y * 2 then x - y else y - x", "if x - y < 0 then 1 else 2", "if 0 < x - y then 1 else 2",
 "if 1 < 2 then x else y", "if 1 - 2 < 1 then x else y", "if 2 == 2 then x else y", "if -1 < 0 then x else y",
 "if 18446744073709551616 < 1 then x else y", "if 18446744073709551616 == 0 then x else y",
 "if x < 18446744073709551616 then 1 else 2", "if x == 18446744073709551616 then 1 else 2",
 "if x < 9223372036854775808 then 1 else 2", "if x <= 9223372036854775807 then 1 else 2",
 "let z := 0 - 1; if z < 5 then 1 else 2", "let z := 0 - 1; if z < x then 1 else 2", "let z := x - 1; if z < 5 then 1 else 2",
 "let z := 0 - 1; if 5 < z then z else x", "let z := (let w := 1; w - 2); if z < 5 then 1 else 2",
 "if (let w := 1; w - 2) < 5 then 1 else 2", "if (let w := x; w - 2) < 5 then 1 else 2",
 "if (if x < y then 1 else 2) < 2 then 3 else 4", "if (if x < y then x else 0 - 1) < 2 then 3 else 4",
 "if x < y then if y < x then 1 else 2 else 3", "if x < y then 1 else if y < x then 2 else 3",
 "if x < y then 1 else 2 + 3", "(if x < y then 1 else 2) + 3", "x + (if x < y then 1 else 2)", "x + if x < y then 1 else 2",
 "if x < y then let z := x; z * z else 0", "if x < y then 1 else let z := y; z - 1", "let z := if x < y then x else y; z + 1",
 "if x < y then (1) else (2)", "if (x < y) then 1 else 2", "if (x) < (y) then 1 else 2", "if x * y < x + y then 1 else 2",
 "if x < y then 1 else 2 * 3", "if x < y then 1 * 2 else 2", "if x == y then x else 0 - x",
 "if x < y\n  then 1\n  else 2", "if x < y then\n  1\nelse\n  2", "if x < y\nthen 1 else 2", "if x < y then 1\n else 2",
 "if\n  x < y then 1 else 2", "if x\n  < y then 1 else 2", "if x <\n  y then 1 else 2", "if x == \n  y then 1 else 2",
 "if x  <  y  then  1  else  2", "iff x < y then 1 else 2", "if1 x < y then 1 else 2", "if x < y thn 1 else 2",
 "if x < y then 1 els 2", "if x < y then 1 else2", "if x < y then1 else 2", "if(x < y) then 1 else 2",
 "if x < y then(1) else 2", "if x < y then 1 else(2)", "if x < y then 1 else 2 else 3", "if x < y then 1 then 2 else 3",
 "if x < y then 1 else 2; 3", "let z := 1; if z < x then z else 2", "let z := 1; if x < z then z else 2",
 "if x < y then x else y - if x < y then 1 else 2", "if x <= y then if x == y then 0 else 1 else 2",
 "if x < y then 18446744073709551615 else 0", "if x < y then -1 else -2", "if x < y then - 1 else - 2",
]
PRE = "def g (a b : T) : T := a - b\ndef k : T := 7\n"
CALLB = [
 "if g x y < 1 then 1 else 2", "if k < 8 then x else y", "if k == 7 then x else y", "if 8 < k then x else y",
 "if g 1 2 < 1 then 1 else 2", "if g (if x < y then x else y) 1 == 0 then 1 else 2",
 "let z := g 0 1; if z < 5 then 1 else 2", "if (if x < y then g 0 1 else 1) < 5 then 1 else 2",
 "if k < 1 - 2 then x else y", "if k - 8 < 1 then x else y",
]
cases = []
for ty in ["UInt64", "Int64"]:
    for b in BODIES: cases.append(case(H2.replace("T", ty) + b, ty))
    for b in CALLB: cases.append(case((PRE + H2).replace("T", ty) + b, ty))
NHAND = len(cases)
# v1 corpus: must be accepted by v2 with the same meaning
for s in CORPUS: cases.append(case(s))
for s in INT_CORPUS: cases.append(case(s, "Int64"))

# random programs with `if`
def gexpr(d, ps, funs, typed_ok):
    r = rng
    if d == 0 or r.random() < .2:
        if ps and r.random() < .75: return r.choice(ps)
        return str(r.choice([0, 1, 2, 3, 5, 255, 2**63, 2**63 - 1, M - 1, M + 3, r.randrange(M)]))
    k = r.random()
    if k < .35:
        return f"({gexpr(d-1, ps, funs, typed_ok)} {r.choice('+-*')} {gexpr(d-1, ps, funs, typed_ok)})"
    if k < .7:
        a = gexpr(d-1, ps, funs, typed_ok); b = gexpr(d-1, ps, funs, typed_ok)
        if r.random() < .8 and ps and not re.search(r"[a-z]", a + b): a = f"({a} + {r.choice(ps)})"
        op = r.choice(["<", "<=", "=="])
        return f"(if {a} {op} {b} then {gexpr(d-1, ps, funs, typed_ok)} else {gexpr(d-1, ps, funs, typed_ok)})"
    if k < .85 and ps:
        x = f"l{r.randrange(9)}"
        return f"(let {x} := {gexpr(d-1, ps, funs, typed_ok)}; {gexpr(d-1, ps + [x], funs, typed_ok)})"
    if funs:
        f, ar = r.choice(funs)
        return f"({f} " + " ".join(f"({gexpr(d-1, ps, funs, typed_ok)})" for _ in range(ar)) + ")" if ar else f
    return gexpr(d-1, ps, funs, typed_ok)

def gprog(ty):
    funs, out = [], []
    for i in range(rng.randrange(1, 4)):
        ar = rng.randrange(1, 4)
        ps = [f"p{j}" for j in range(ar)]
        body = gexpr(rng.randrange(1, 5), ps, funs, True)
        if body.startswith("(") and rng.random() < .5:
            d, ok = 0, True
            for j, c in enumerate(body):
                d += (c == "(") - (c == ")")
                if d == 0 and j < len(body) - 1: ok = False
            if ok: body = body[1:-1]
        out.append(f"def g{i} ({' '.join(ps)} : {ty}) : {ty} := {body}")
        funs.append((f"g{i}", ar))
    return "\n".join(out)

for _ in range(N):
    ty = rng.choice(["UInt64", "Int64"])
    p = gprog(ty)
    if rng.random() < .25:  # token mutation
        ts = re.findall(r"\w+|:=|<=|==|\S", p)
        i = rng.randrange(len(ts)); op = rng.random()
        if op < .3: del ts[i]
        elif op < .6: ts.insert(i, rng.choice(["if", "then", "else", "<", "<=", "==", "(", ")", "x", "1", "-", "=", ">"]))
        else: ts[i], ts[(i + 1) % len(ts)] = ts[(i + 1) % len(ts)], ts[i]
        p = " ".join(ts).replace(" := ", " := ").replace("def ", "\ndef ").strip()
    cases.append(case(p, ty))

inp = "\n".join(json.dumps(c) for c in cases) + "\n"
out = subprocess.run("PATH=$HOME/.elan/bin:$PATH lake env lean --run Testing/nano/oracle2.lean", shell=True, cwd=ROOT,
                     input=inp, capture_output=True, text=True)
if out.returncode: print(out.stderr[-3000:]); sys.exit(2)
lines = out.stdout.splitlines(); assert len(lines) == len(cases), (len(lines), len(cases))
stat = dict(both_reject=0, nano_only_rejects=0, both_accept_equal=0, both_accept_unevaluated=0,
            BUG_nano_accepts_lean_rejects=0, BUG_meanings_differ=0)
bugs, rows = [], []
for i, (c, l) in enumerate(zip(cases, lines)):
    r, n = l.split(" nano="); r = r[len("real="):]
    if r == "R" and n == "R": v = "both_reject"
    elif r != "R" and n == "R": v = "nano_only_rejects"
    elif r == "R": v = "BUG_nano_accepts_lean_rejects"; bugs.append((c["src"], l))
    elif "?" in r: v = "both_accept_unevaluated"
    elif r == n: v = "both_accept_equal"
    else: v = "BUG_meanings_differ"; bugs.append((c["src"], l))
    stat[v] += 1
    if i < NHAND and "--table" in sys.argv: rows.append((c, r, n, v))
print(len(cases), "cases:", stat)
if "--table" in sys.argv:
    t = ["| type | text | Lean | nano | verdict |", "|---|---|---|---|---|"]
    for c, r, n, v in rows:
        sh = lambda z: "reject" if z == "R" else "accept " + z[2:-1].split(",")[0]
        body = c["src"].split(":= ", 1)[1] if c["src"].startswith("def f") else c["src"].split("\n")[-1]
        t.append(f"| {c['ty']} | `{body.replace(chr(10), '\\n').replace('|', '\\|')}` | {sh(r)} | {sh(n)} | {v} |")
    print("\n".join(t))
for s, l in bugs[:20]: print("BUG", repr(s), l)
sys.exit(1 if bugs else 0)
