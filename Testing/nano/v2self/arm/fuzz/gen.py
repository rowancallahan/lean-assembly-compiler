# gen.py: random nano programs that stress control flow (UNPROVEN test tool, not part of the proof).
# gen(seed) → source text (nano subset, no comments). Helpers h<j> and fuel recursions g<j> form a DAG
# (helpers call only lower helpers; fuel functions call helpers and themselves once); entry m is one of:
# a fuel-driven accumulator loop writing output (o1), or a single fuel-recursion result as one byte.
import random

PARAMS = "abcdpqstuvw"   # UInt64 parameters (single letters, as the nano lexer requires)
LETS = "yzr"            # let-bound locals

class Body:
    def __init__(self, rng, scope, helpers, budget):
        self.rng, self.scope, self.helpers, self.budget = rng, scope, helpers, budget

    def lit(self):
        r = self.rng
        k = r.random()
        if k < 0.5: return str(r.randint(0, 20))
        if k < 0.7: return str(r.choice([255, 256, 65535, 2**32 - 1, 2**63, 2**64 - 1, 63, 64, 65]))
        return str(r.getrandbits(64))

    def leaf(self):
        r = self.rng
        if self.scope and r.random() < 0.7: return r.choice(self.scope), 0
        return self.lit(), 0

    def call(self, d):
        ok = [h for h in self.helpers if h["cost"] + 1 <= self.budget[0]]
        if not ok: return self.leaf()
        h = self.rng.choice(ok)
        self.budget[0] -= h["cost"] + 1
        parts, c = ["h%d" % h["id"] if h["kind"] == "h" else "g%d" % h["id"]] , h["cost"] + 1
        args = ["x"]
        for _ in range(h["arity"]):
            s, cc = self.expr(max(d - 2, 0))
            args.append("(" + s + ")"); c += cc
        return parts[0] + " " + " ".join(args), c

    def expr(self, d):
        r, rng = self.rng, self.rng
        k = r.random()
        if d <= 0 or k < 0.22: return self.leaf()
        if k < 0.46:
            op = r.choice(["+", "-", "*", "&&&", "|||", "+", "-"])
            a, ca = self.expr(d - 1); b, cb = self.expr(d - 1)
            return "(%s %s %s)" % (a, op, b), ca + cb
        if k < 0.54:
            a, ca = self.expr(d - 1)
            return "(%s %s %d)" % (a, r.choice(["<<<", ">>>"]), r.randint(0, 70)), ca
        if k < 0.66 and self.helpers:
            return self.call(d)
        if k < 0.78:
            s, cs = self.expr(d - 1)
            return "rd x (%s)" % s, cs
        if k < 0.82:
            return "len x", 0
        c1, cc1 = self.cond(d - 1)
        t, ct = self.expr(d - 1); f, cf = self.expr(d - 1)
        return "(if %s then %s else %s)" % (c1, t, f), cc1 + max(ct, cf)

    def cond(self, d):
        a, ca = self.expr(d); b, cb = self.expr(d)
        return "%s %s %s" % (a, self.rng.choice(["==", "<", "=="]), b), ca + cb

    def let_body(self, d, names):
        # optional lets, then final expression
        lines, c = [], 0
        for nm in names:
            s, cs = self.expr(d)
            lines.append("let %s := %s;" % (nm, s)); c += cs
            self.scope.append(nm)
        e, ce = self.expr(d)
        return "\n    ".join(lines + [e]) if lines else e, c + ce

def long_chain(rng, scope, helpers, n):
    # if-chain with n branches: large functions (long forward branches)
    parts, c = [], 0
    for _ in range(n):
        b = Body(rng, scope, helpers, [10**9])
        cond, cc = b.cond(1); e, ce = b.expr(1)
        parts.append("if %s then %s else" % (cond, e)); c += cc + ce
    b = Body(rng, scope, helpers, [10**9]); last, cl = b.expr(1)
    return "\n    ".join(parts + [last]), c + cl

def gen(seed):
    rng = random.Random(seed)
    mode = rng.random()
    nh = rng.choice([1, 2, 3, 5, 8, 12, 20, 30]) if mode < 0.9 else rng.randint(40, 70)
    helpers, out = [], []
    long_fn = rng.random() < 0.08
    for j in range(1, nh + 1):
        arity = rng.randint(0, 5)
        names = rng.sample(PARAMS, arity)
        scope = list(names)
        params = " ".join("(%s : UInt64)" % p for p in names)
        budget = [rng.choice([6, 30, 120, 300])]
        if long_fn and j == nh:
            body, cost = long_chain(rng, list(scope), helpers, rng.randint(50, 400))
        else:
            lets = rng.sample(LETS, rng.randint(0, 2))
            body, cost = Body(rng, scope, helpers, budget).let_body(rng.randint(1, 4), lets)
        helpers.append({"id": j, "kind": "h", "arity": arity, "cost": cost})
        out.append("def h%d (x : List UInt8) %s : UInt64 :=\n    %s" % (j, params, body))
    # fuel recursions g<k> (call helpers; one self call)
    fuel_fns = []
    for k in range(1, rng.randint(1, 4) + 1):
        arity = rng.randint(1, 4)
        names = rng.sample(PARAMS, arity)
        scope = list(names)
        ext = [dict(h) for h in helpers]
        ub = [rng.choice([20, 60])]
        b0 = Body(rng, list(scope), ext, [rng.choice([10, 40])])
        base, c0 = b0.expr(rng.randint(1, 3))
        b1 = Body(rng, list(scope), ext, [40])
        self_args = []
        for _ in range(1 + arity):
            s, cs = b1.expr(2); self_args.append("(%s)" % s); c0 += cs
        selfcall = "g%d n x %s" % (k, " ".join(self_args[1:]))
        ncond, nc = b1.cond(1); alt, ca = b1.expr(2)
        if rng.random() < 0.5:
            step = "(if %s then %s else %s)" % (ncond, selfcall, alt)
        else:
            step = "(%s)" % selfcall
        pats = ", ".join(names)
        fargs = "".join(" UInt64 →" for _ in names)
        fuel_fns.append((k, arity))
        out.append("def g%d : Nat → List UInt8 →%s UInt64\n  | 0, x, %s => %s\n  | n + 1, x, %s => %s"
                   % (k, fargs, pats, base, pats, step) if arity else
                   "def g%d : Nat → List UInt8 → UInt64\n  | 0, x => %s\n  | n + 1, x => %s" % (k, base, step))
    # entry
    kind = rng.random()
    fuel_name, fuel_arity = rng.choice(fuel_fns) if fuel_fns else (None, 0)
    if kind < 0.5 or fuel_name is None:
        # accumulator loop over the input writing one byte per step
        sc = ["i", "a"]
        ext = [dict(h) for h in helpers]
        bA = Body(rng, list(sc), ext, [60]); newa, _ = bA.expr(rng.randint(1, 3))
        bB = Body(rng, list(sc), ext, [60]); byte, _ = bB.expr(rng.randint(1, 3))
        out.append("def o1 : Nat → List UInt8 → UInt64 → UInt64 → List UInt8 → List UInt8\n"
                   "  | 0, x, i, a, o => o\n"
                   "  | n + 1, x, i, a, o => if i < len x then o1 n x (i + 1) (%s) (put o (%s)) else o" % (newa, byte))
        out.append("def m (x : List UInt8) : List UInt8 := o1 %s x 0 %d []"
                   % (rng.choice(["(len' x)", "(len' x)", "100000"]), rng.randint(0, 999)))
    else:
        fuel = rng.choice(["(len' x)", "(len' x)", "5", "0", "100000", "1000000"])
        n_out = rng.choice([1, 1, 2, 8])
        fa = " ".join("(%s)" % rng.choice(["7", "rd x 0", "len x", "rd x 1 + 3"]) for _ in range(fuel_arity))
        if n_out == 1:
            body = "put [] (g%d %s x %s)" % (fuel_name, fuel, fa)
        else:
            body = "put (put [] (g%d %s x %s)) ((g%d %s x %s) >>> 8)" % (fuel_name, fuel, fa, fuel_name, fuel, fa)
        out.append("def m (x : List UInt8) : List UInt8 := %s" % body)
    return "\n".join(out) + "\n"
