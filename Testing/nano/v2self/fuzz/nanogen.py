#!/usr/bin/env python3
"""Random nano programs for the whole-program differential fuzzer (fuzz/nanofuzz.py).
usage: nanogen.py SEED N DIR
Writes DIR/g{i}.src for i < N (no comments; nanofuzz.py adds mutations and comments itself).
Shape: helper defs (binder style, UInt64 or List UInt8 result), one fuel-recursive def in the examples' pattern,
entry `m`.  Valid-biased: every def uses only the accepted constructs (see examples/README.md).  Not every program is
guaranteed accepted; the driver compares the compiler with the reference semantics either way."""
import random, sys, os

R = random.Random(int(sys.argv[1]))
N = int(sys.argv[2]); DIR = sys.argv[3]
# letters for locals and helper names; x i o n m are reserved (input, index, accumulator, fuel, entry)
ALPHA = 'abcdefghjklpqrstuvwyz'
BIN = ['+', '-', '*', '&&&', '|||']   # `^^^` is rejected by B2 (see summary: GAP check)
CMP = ['==', '<']

class Gen:
    def __init__(s):
        s.used = set(); s.defs = []   # (name, kind, params) kind: 'u' (UInt64) or 'l' (List UInt8)
    def name(s):
        while True:
            nm = R.choice(ALPHA) + (str(R.randrange(1, 100)) if R.random() < 0.6 else '')
            if nm not in s.used:
                s.used.add(nm); return nm
    def num(s):
        r = R.random()
        if r < 0.7: return str(R.randrange(0, 40))
        if r < 0.9: return str(R.randrange(0, 300))
        if r < 0.97: return str(R.randrange(0, 2**16))
        return str(2**64 - 1 - R.randrange(0, 4))

    # expression of type 'u' (UInt64) or 'l' (List UInt8)
    # env: list of (name, type); fz: None or the fuel def's (name) when a self call is allowed at tail position
    def ge(s, ty, env, d, tail=False, fz=None):
        vars_ = [n for n, t in env if t == ty]
        if d <= 0 or R.random() < 0.15:
            return s.leaf(ty, env, vars_)
        r = R.random()
        if ty == 'u':
            if r < 0.22:
                return f"({s.ge('u', env, d-1)} {R.choice(BIN)} {s.ge('u', env, d-1)})"
            if r < 0.28:
                return f"({s.ge('u', env, d-1)} {R.choice(['<<<', '>>>'])} {R.randrange(0, 64)})"
            if r < 0.40:
                return s.cond(env, d, 'u')
            if r < 0.50:
                return s.let(env, d, 'u', tail, fz)
            if r < 0.62:
                return f"(rd x {s.ge('u', env, d-1)})"
            if r < 0.66:
                return "(len x)"
            return s.call('u', env, d) or s.leaf(ty, env, vars_)
        # list
        if fz and tail and R.random() < 0.35:
            return s.selfcall(env, d, fz)
        if r < 0.45:
            return f"(put {s.ge('l', env, d-1)} {s.ge('u', env, d-1)})"
        if r < 0.60:
            return s.cond(env, d, 'l', tail, fz)
        if r < 0.70:
            return s.let(env, d, 'l', tail, fz)
        return s.call('l', env, d) or s.leaf(ty, env, vars_)

    def leaf(s, ty, env, vars_):
        if ty == 'u':
            if vars_ and R.random() < 0.7: return R.choice(vars_)
            return s.num()
        # B2 rejects the input x as a list value (`return x`, `put x 1`); x is only passed as an argument
        lists = [n for n, t in env if t == 'l' and n != 'x']
        return R.choice(lists + ['[]'])

    def cond(s, env, d, ty, tail=False, fz=None):
        # B2 rejects a parenthesized condition: `if A < B then ...` inside the parentheses of the if
        c = f"{s.ge('u', env, d-1)} {R.choice(CMP)} {s.ge('u', env, d-1)}"
        return f"(if {c} then {s.ge(ty, env, d-1, tail, fz)} else {s.ge(ty, env, d-1, tail, fz)})"

    def let(s, env, d, ty, tail=False, fz=None):
        v = s.name()
        vt = 'u' if R.random() < 0.7 else 'l'
        e = s.ge(vt, env, d-1)
        return f"(let {v} := {e}; {s.ge(ty, env + [(v, vt)], d-1, tail, fz)})"

    def call(s, ty, env, d):
        cands = [(nm, ps) for nm, k, ps in s.defs if k == ty]
        if not cands: return None
        nm, ps = R.choice(cands)
        args = ['x'] + [('x' if t == 'l' and R.random() < 0.3 else s.ge(t, env, d-1)) for t in ps]
        return f"({nm} " + ' '.join(args) + ")"

    def selfcall(s, env, d, fz):
        # fuel n, input x, index, accumulator.  B2 rejects a bare accumulator variable here (`g n x i o`), so the
        # accumulator argument is a put.  The self call is the last thing of its branch.
        return f"({fz} n x {s.ge('u', env, d-1)} (put {s.ge('l', env, d-1)} {s.ge('u', env, d-1)}))"

    def tailbody(s, env, d, fz):
        # the n + 1 branch must contain the self call (B2 rejects a branch without one)
        r = R.random()
        if r < 0.5 or d <= 1: return s.selfcall(env, d, fz)
        if r < 0.75: return f"(if {s.ge('u', env, d-1)} {R.choice(CMP)} {s.ge('u', env, d-1)} then {s.tailbody(env, d-1, fz)} else {s.tailbody(env, d-1, fz)})"
        v = s.name(); vt = 'u'
        return f"(let {v} := {s.ge(vt, env, d-1)}; {s.tailbody(env + [(v, vt)], d-1, fz)})"

    def helper(s):
        nm = s.name(); ty = R.choice(['u', 'u', 'l'])
        ps = [R.choice(['u', 'u', 'u', 'l']) for _ in range(R.randrange(0, 3))]
        names = [s.name() for _ in ps]
        env = [('x', 'l')] + [(n, t) for n, t in zip(names, ps)]
        body = s.ge(ty, env, R.randrange(2, 5))
        sig = ' '.join(f"({n} : {'UInt64' if t == 'u' else 'List UInt8'})" for n, t in zip(names, ps))
        rt = 'UInt64' if ty == 'u' else 'List UInt8'
        s.defs.append((nm, ty, ps))
        return f"def {nm} (x : List UInt8) {sig} : {rt} := {body}\n"

    def fuel(s):
        nm = s.name()
        env_b = [('x', 'l'), ('i', 'u'), ('o', 'l')]
        b0 = s.ge('l', env_b, R.randrange(1, 4))
        b1 = s.tailbody(env_b, R.randrange(2, 5), nm)
        s.defs.append((nm, 'l', ['u', 'l']))   # the fuel def takes (x, i, o) with fuel n in front
        return (f"def {nm} : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8\n"
                f"  | 0, x, i, o => {b0}\n"
                f"  | n + 1, x, i, o => {b1}\n")

    def entry(s, fz):
        fuel = R.choice(["(len' x)", "(len' x)", str(R.randrange(0, 30))])   # B2 rejects `len' x + k` as fuel
        return f"def m (x : List UInt8) : List UInt8 := {fz} {fuel} x 0 []\n"

def program():
    g = Gen()
    out = [g.helper() for _ in range(R.randrange(0, 4))]
    out.append(g.fuel())
    out.append(g.entry(g.defs[-1][0]))
    return ''.join(out)

if __name__ == '__main__':
    os.makedirs(DIR, exist_ok=True)
    for i in range(N):
        with open(os.path.join(DIR, f"g{i}.src"), 'w') as f:
            f.write(program())
