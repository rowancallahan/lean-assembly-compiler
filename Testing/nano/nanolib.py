"""nano test corpus, random program generator, helpers."""
import random, re
M = 2 ** 64
CORPUS = [
"def f (x : UInt64) : UInt64 := x",
"def f (x : UInt64) : UInt64 := 42",
"def f (x y : UInt64) : UInt64 := x + y",
"def f (x y : UInt64) : UInt64 := x - y",
"def f (x y : UInt64) : UInt64 := x * y",
"def f (x y : UInt64) : UInt64 := x + y * 2",
"def f (x y : UInt64) : UInt64 := (x + y) * 2",
"def f (x y : UInt64) : UInt64 := x - y - 1",
"def f (x y z : UInt64) : UInt64 := x * y + z * 3 - 7",
"def f (x : UInt64) : UInt64 := 18446744073709551615 + x",
"def f (x : UInt64) : UInt64 := x * 18446744073709551616 + 1",
"def f (x : UInt64) : UInt64 := let y := x + 1; y * y",
"def f (x : UInt64) : UInt64 := let y := x + 1; let z := y * 2; z - y + x",
"def f (x y : UInt64) : UInt64 := let x := y + 1; x * 2",
"def f (x : UInt64) : UInt64 := (let y := x * x; y + 1) + 5",
"def sq (x : UInt64) : UInt64 := x * x\ndef f (x : UInt64) : UInt64 := sq x + 1",
"def sq (x : UInt64) : UInt64 := x * x\ndef f (x y : UInt64) : UInt64 := sq (x + y) - sq x - sq y",
"def add3 (a b c : UInt64) : UInt64 := a + b + c\ndef f (x y : UInt64) : UInt64 := add3 x y 7",
"def add3 (a b c : UInt64) : UInt64 := a + b * c\ndef f (x y : UInt64) : UInt64 := add3 x (y - 1) (x + 2) * 2",
"def k : UInt64 := 1000\ndef f (x : UInt64) : UInt64 := x + k",
"def k : UInt64 := 1000\ndef g (x : UInt64) : UInt64 := x * k\ndef f (x : UInt64) : UInt64 := g (g x) + k",
"def inc (x : UInt64) : UInt64 := x + 1\ndef inc2 (x : UInt64) : UInt64 := inc (inc x)\ndef inc4 (x : UInt64) : UInt64 := inc2 (inc2 x)\ndef f (x : UInt64) : UInt64 := inc4 (inc4 x)",
"def f (a b c d : UInt64) : UInt64 := a - b - c - d",
"def f (a b c d : UInt64) : UInt64 := a * b * c * d",
"def f (a b c d : UInt64) : UInt64 := a + b * c - d",
"def f (a b c d : UInt64) : UInt64 := (a - b) * (c - d)",
"def f (x : UInt64) : UInt64 := 0 - x",
"def f (x : UInt64) : UInt64 := x * 0 + 0 * x",
"def f (x : UInt64) : UInt64 := ((((x))))",
"def mix (a b : UInt64) : UInt64 := a * 31 + b\ndef f (x y z : UInt64) : UInt64 := mix (mix x y) z",
"def f (x y : UInt64) : UInt64 :=\n  let s := x + y\n  ; let d := x - y\n  ; s * d",
"def f (x : UInt64) : UInt64 := let a := x; let b := a; let c := b; c - a + 3",
"def g (x y : UInt64) : UInt64 := x - y\ndef f (x : UInt64) : UInt64 := g 5 x",
"def g (x y : UInt64) : UInt64 := x - y\ndef f (x : UInt64) : UInt64 := g x 5 * g 5 x",
"def f (x : UInt64) : UInt64 := let y := x * 2; y * y * y - x",
"def f (x : UInt64) : UInt64 := 1 + 2 * 3 - 4 + x",
"def f (xs ys : UInt64) : UInt64 := xs * ys + xs - ys",
"def f (x_1 x_2 : UInt64) : UInt64 := x_1 * x_2 + 1",
"def h (x : UInt64) : UInt64 := x + 3\ndef g (x : UInt64) : UInt64 := h x * h (x + 1)\ndef f (x : UInt64) : UInt64 := g (g x)",
]
NEG = [  # must be rejected by nanoElab (not valid nano)
"def f (x : UInt64) : UInt64 := y",
"def f (x : UInt64) : UInt64 := x +",
"def f (x : UInt64) : UInt64 := g x",
"def g (x y : UInt64) : UInt64 := x\ndef f (x : UInt64) : UInt64 := g x",
"def f (x : UInt64) : UInt64 := (x",
"def f (x : UInt64) : UInt64 := x $ 1",
"def f x : UInt64 := x",

"def f (x : UInt64) : UInt64 := let y := x x",
]
def entry_arity(src):
    m = re.findall(r"^def\s+\w+((?:\s*\([^)]*\))*)\s*:", src, re.M)[-1]
    return sum(len(g.split(":")[0].split()) for g in re.findall(r"\(([^)]*)\)", m))
EDGE = [0, 1, 2, 3, 7, 255, 2**32, 2**63, M - 2, M - 1]
def inputs(rng, k, n=6):
    return [[rng.choice(EDGE) if rng.random() < .5 else rng.randrange(M) for _ in range(k)] for _ in range(n)]

class G:
    def __init__(s, rng): s.rng = rng
    def expr(s, depth, params, funs, typed):
        r = s.rng
        # typed: expression already has a determined UInt64 type context by a variable/call (for let values)
        leaves = [("n", None)] + [("v", p) for p in params]
        if depth == 0 or r.random() < .25:
            if params and (typed or r.random() < .7): return r.choice(params)
            if typed: return r.choice(params)
            return str(r.choice([0, 1, 2, 3, 10, 255, 12345, M - 1, M + 5, r.randrange(M)]))
        k = r.random()
        if k < .5:
            a = s.expr(depth - 1, params, funs, typed); b = s.expr(depth - 1, params, funs, typed)
            return f"({a} {r.choice('+-*')} {b})" if r.random() < .5 else f"{s.atomwrap(a)} {r.choice('+-*')} {s.atomwrap(b)}"
        if k < .7 and params:
            v = s.expr(depth - 1, params, funs, True)
            x = f"l{r.randrange(100)}"
            return f"(let {x} := {v}; {s.expr(depth - 1, params + [x], funs, typed)})"
        if funs:
            f, ar = r.choice(funs)
            args = " ".join(s.atom(depth - 1, params, funs, typed) for _ in range(ar))
            return f"({f} {args})" if ar else f
        return s.expr(depth - 1, params, funs, typed)
    def atomwrap(s, e):  # operand of an operator: parens unless atom-like
        return e if re.fullmatch(r"\w+|\(.*\)", e) and e.count("(") == e.count(")") and (e[0] != "(" or s.balanced(e)) else f"({e})"
    def balanced(s, e):
        d = 0
        for i, c in enumerate(e):
            d += (c == "(") - (c == ")")
            if d == 0 and i < len(e) - 1: return False
        return True
    def atom(s, depth, params, funs, typed):
        e = s.expr(depth, params, funs, typed)
        return e if (re.fullmatch(r"\w+", e) or (e.startswith("(") and s.balanced(e))) else f"({e})"
    def program(s):
        r = s.rng; funs = []; out = []
        for i in range(r.randrange(1, 4)):
            ar = r.randrange(0, 4) if i < 2 else r.randrange(1, 4)
            if i == 0 and ar == 0 and r.random() < .5: ar = 1
            ps = [f"p{j}" for j in range(ar)]
            name = f"g{i}"
            body = s.expr(r.randrange(1, 5), ps, funs, False) if ps else str(r.randrange(M))
            if ps and r.random() < .0: pass
            out.append(f"def {name} " + (f"({' '.join(ps)} : UInt64) " if ps else "") + f": UInt64 := {body}")
            funs.append((name, ar))
        # entry: last def takes 1..3 params
        return "\n".join(out)
