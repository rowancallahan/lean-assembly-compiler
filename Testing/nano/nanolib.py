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
"def s (x : UInt64) : UInt64 := x * x\ndef f (x : UInt64) : UInt64 := s x + 1",
"def s (x : UInt64) : UInt64 := x * x\ndef f (x y : UInt64) : UInt64 := s (x + y) - s x - s y",
"def a3 (a b c : UInt64) : UInt64 := a + b + c\ndef f (x y : UInt64) : UInt64 := a3 x y 7",
"def a3 (a b c : UInt64) : UInt64 := a + b * c\ndef f (x y : UInt64) : UInt64 := a3 x (y - 1) (x + 2) * 2",
"def k : UInt64 := 1000\ndef f (x : UInt64) : UInt64 := x + k",
"def k : UInt64 := 1000\ndef g (x : UInt64) : UInt64 := x * k\ndef f (x : UInt64) : UInt64 := g (g x) + k",
"def i (x : UInt64) : UInt64 := x + 1\ndef i2 (x : UInt64) : UInt64 := i (i x)\ndef i4 (x : UInt64) : UInt64 := i2 (i2 x)\ndef f (x : UInt64) : UInt64 := i4 (i4 x)",
"def f (a b c d : UInt64) : UInt64 := a - b - c - d",
"def f (a b c d : UInt64) : UInt64 := a * b * c * d",
"def f (a b c d : UInt64) : UInt64 := a + b * c - d",
"def f (a b c d : UInt64) : UInt64 := (a - b) * (c - d)",
"def f (x : UInt64) : UInt64 := 0 - x",
"def f (x : UInt64) : UInt64 := x * 0 + 0 * x",
"def f (x : UInt64) : UInt64 := ((((x))))",
"def m (a b : UInt64) : UInt64 := a * 31 + b\ndef f (x y z : UInt64) : UInt64 := m (m x y) z",
"def f (x y : UInt64) : UInt64 :=\n  let s := x + y\n  ; let d := x - y\n  ; s * d",
"def f (x : UInt64) : UInt64 := let a := x; let b := a; let c := b; c - a + 3",
"def g (x y : UInt64) : UInt64 := x - y\ndef f (x : UInt64) : UInt64 := g 5 x",
"def g (x y : UInt64) : UInt64 := x - y\ndef f (x : UInt64) : UInt64 := g x 5 * g 5 x",
"def f (x : UInt64) : UInt64 := let y := x * 2; y * y * y - x",
"def f (x : UInt64) : UInt64 := 1 + 2 * 3 - 4 + x",
"def f (u v : UInt64) : UInt64 := u * v + u - v",
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

# ---- Int64 (branch nano-mvp) ----
INT_CORPUS = [
"def f (x : Int64) : Int64 := x",
"def f (x : Int64) : Int64 := -5",
"def f (x : Int64) : Int64 := (-5)",
"def f (x y : Int64) : Int64 := x + y",
"def f (x y : Int64) : Int64 := x - y",
"def f (x y : Int64) : Int64 := x * y",
"def f (x : Int64) : Int64 := x * -5",
"def f (x : Int64) : Int64 := -5 + x",
"def f (x : Int64) : Int64 := x - -5",
"def f (x : Int64) : Int64 := -5 * x + -3",
"def f (x : Int64) : Int64 := - 7 - x",
"def f (x : Int64) : Int64 := 9223372036854775807 + x",
"def f (x : Int64) : Int64 := -9223372036854775808 - x",
"def f (x : Int64) : Int64 := 18446744073709551615 * x",
"def f (x : Int64) : Int64 := -99999999999999999999 + x",
"def g (x : Int64) : Int64 := x - 1\ndef f (x : Int64) : Int64 := g (-5) * g x",
"def g (x y : Int64) : Int64 := x * y\ndef f (x y : Int64) : Int64 := g (-x0p) y",
"def f (x : Int64) : Int64 := let y := x * -1; y + y",
"def s (x : Int64) : Int64 := x * x\ndef f (x y : Int64) : Int64 := s (x - y) - s x - s y",
"def k : Int64 := -1000\ndef f (x : Int64) : Int64 := x * k + k",
"def f (a b c d : Int64) : Int64 := (a - b) * (c - d) - -1",
"def m (a b : Int64) : Int64 := a * -31 + b\ndef f (x y z : Int64) : Int64 := m (m x y) z",
"def f (x y : Int64) : Int64 :=\n  let s := x + y\n  ; let d := x - y\n  ; s * d * -2",
"def f (x : Int64) : Int64 := (((-(3))))",
"def f (x : Int64) : Int64 := 9223372036854775808 + x",
"def f (x : Int64) : Int64 := 18446744073709551621 * x",
"def f (x : Int64) : Int64 := 0 - -9223372036854775808",
"def f (x : Int64) : Int64 := -9223372036854775808 * -1 + x",
"def k : Int64 := -1\ndef f (x : Int64) : Int64 := k -1",
]
INT_CORPUS = [s for s in INT_CORPUS if "x0p" not in s and "-(" not in s]  # `-x`, `-(e)`: not nano (Lean accepts; nano rejects)
INT_NEG = [  # Lean rejects or means something else; nanoElab must reject
"def f (x : Int64) : UInt64 := x",
"def f (x : UInt64) : Int64 := x",
"def g (x : Int64) : Int64 := x\ndef f (x : Int64) : Int64 := g -5",
"def f (x : Int64) : Int64 := x --5",
"def f (x : Int64) : Int64 := -x",
"def f (x : Int64) : Int64 := x * - - 5",
"def f (x : Int64) : Int64 := - -5",
"def f (x y : Int64) : Int64 := x - -y",
"def f (x : UInt64) (y : Int64) : Int64 := y",
]
M63 = 2 ** 63
EDGE_I = [0, 1, -1, 2, -2, 7, -7, 255, -256, 2**32, -2**32, M63 - 1, -M63, M63 - 2, -M63 + 1]
def inputs_i(rng, k, n=6):
    return [[rng.choice(EDGE_I) if rng.random() < .6 else rng.randrange(-M63, M63) for _ in range(k)] for _ in range(n)]
def signed(v): v %= M; return v - M if v >= M63 else v

class GI(G):
    """random nano programs over a type `T`, with negative numerals where Lean reads them as `Neg.neg` of a literal"""
    def __init__(s, rng, T="Int64"): super().__init__(rng); s.T = T
    def expr(s, depth, params, funs, typed):
        r = s.rng
        if depth == 0 or r.random() < .25:
            if params and (typed or r.random() < .7): return r.choice(params)
            if typed: return r.choice(params)
            n = str(r.choice([0, 1, 2, 3, 10, 255, 12345, M63 - 1, M63, M - 1, M + 5, r.randrange(M)]))
            return ("-" + n) if r.random() < .4 else n
        k = r.random()
        if k < .5:
            a = s.expr(depth - 1, params, funs, typed); b = s.expr(depth - 1, params, funs, typed)
            if r.random() < .5: return f"({a} {r.choice('+-*')} {b})"
            wa = a if re.fullmatch(r"-\d+", a) and r.random() < .5 else s.atomwrap(a)
            wb = b if re.fullmatch(r"-\d+", b) and r.random() < .5 else s.atomwrap(b)
            return f"{wa} {r.choice('+-*')} {wb}"
        if k < .7 and params:
            v = s.expr(depth - 1, params, funs, True)
            x = f"l{r.randrange(100)}"
            return f"(let {x} := {v}; {s.expr(depth - 1, params + [x], funs, typed)})"
        if funs:
            f, ar = r.choice(funs)
            args = " ".join(s.atom(depth - 1, params, funs, typed) for _ in range(ar))
            return f"({f} {args})" if ar else f
        return s.expr(depth - 1, params, funs, typed)
    def program(s):
        r = s.rng; funs = []; out = []
        for i in range(r.randrange(1, 4)):
            ar = r.randrange(0, 4) if i < 2 else r.randrange(1, 4)
            if i == 0 and ar == 0 and r.random() < .5: ar = 1
            ps = [f"p{j}" for j in range(ar)]
            body = s.expr(r.randrange(1, 5), ps, funs, False) if ps else str(r.randrange(M))
            out.append(f"def g{i} " + (f"({' '.join(ps)} : {s.T}) " if ps else "") + f": {s.T} := {body}")
            funs.append((f"g{i}", ar))
        return "\n".join(out)
