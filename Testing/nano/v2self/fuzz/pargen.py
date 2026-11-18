#!/usr/bin/env python3
"""Random typed S programs (valid-biased) + token-level mutations, for the Par1 vs ParSpec differential.
usage: pargen.py DIR N SEED  -> DIR/p{i}.txt (mutated when i is odd)"""
import random, sys, os
R = random.Random(int(sys.argv[3]))
W = 'w'
def sstr(s, top=True):
    if s == W: return 'UInt64'
    a = sstr(s[1], False); b = sstr(s[2], True)
    t = f"{a} × {b}"
    return t if top else f"({t})"
def rshape(d=2):
    if d == 0 or R.random() < 0.6: return W
    return ('p', rshape(d-1), rshape(d-1))
class G:
    def __init__(s):
        s.defs = []; s.cnt = 0; s.loopctx = None
    def fresh(s):
        s.cnt += 1; return R.choice('abcdefghjkqrstuvwxyz') + str(s.cnt) + (str(R.randrange(0, 3)) if R.random() < 0.3 else '')
    def shapevars(s, env, sh): return [n for n, t in env if t == sh]
    def expr(s, sh, env, d, tail, inp, top=False):
        r = s.expr0(sh, env, d, tail, inp)
        return r if top or not (r.startswith('if ') or r.startswith('let ')) else '(' + r + ')'
    def expr0(s, sh, env, d, tail, inp):
        """env: list of (name, shape) innermost LAST; inp = input name or None"""
        c = R.random()
        if d <= 0: return s.leaf(sh, env, inp)
        if tail and s.loopctx and R.random() < 0.35:
            return s.selfcall(env, d, inp)
        if c < 0.12: return s.leaf(sh, env, inp)
        if c < 0.30:  # if
            a = s.expr(W, env, d-1, False, inp); b = s.expr(W, env, d-1, False, inp)
            return f"if {a} {R.choice(['==','<'])} {b} then {s.expr(sh, env, d-1, tail, inp, True)} else {s.expr(sh, env, d-1, tail, inp, True)}"
        if c < 0.45:  # let
            vs = rshape(1); n = s.fresh()
            v = s.expr(vs, env, d-1, False, inp)
            return f"let {n} := {v}; {s.expr(sh, env + [(n, vs)], d-1, tail, inp, True)}"
        if c < 0.55:  # pair let
            l, r = rshape(1), rshape(1); n1, n2 = s.fresh(), s.fresh()
            v = s.expr(('p', l, r), env, d-1, False, inp)
            return f"let ({n1}, {n2}) := {v}; {s.expr(sh, env + [(n1, l), (n2, r)], d-1, tail, inp, True)}"
        if sh != W:
            if c < 0.8: return f"({s.expr(sh[1], env, d-1, False, inp)}, {s.expr(sh[2], env, d-1, False, inp)})"
            return s.call(sh, env, d, inp) or s.leaf(sh, env, inp)
        # word
        if c < 0.75:
            op = R.choice(['+', '-', '*', '&&&', '|||'])
            return f"({s.expr(W, env, d-1, False, inp)} {op} {s.expr(W, env, d-1, False, inp)})" if R.random() < 0.5 else f"{s.expr(W, env, d-1, False, inp)} {op} {s.expr(W, env, d-1, False, inp)}" if False else f"({s.expr(W, env, d-1, False, inp)} {op} {s.expr(W, env, d-1, False, inp)})"
        if c < 0.82: return f"({s.expr(W, env, d-1, False, inp)} {R.choice(['<<<', '>>>'])} {R.randrange(0, 64)})"
        if c < 0.92:
            r = s.call(sh, env, d, inp)
            if r: return r
        return s.prim(env, d, inp)
    def leaf(s, sh, env, inp):
        vs = s.shapevars(env, sh)
        if vs and R.random() < 0.7: return R.choice(vs)
        if sh == W:
            if inp and R.random() < 0.3: return f"(rd {inp} {R.randrange(0, 5)})"
            return str(R.choice([0, 1, 2, 7, 255, R.randrange(0, 2**20), 2**64 - 1]))
        return f"({s.leaf(sh[1], env, inp)}, {s.leaf(sh[2], env, inp)})"
    def prim(s, env, d, inp):
        c = R.random(); e = lambda: s.expr(W, env, d-1, False, inp)
        if inp and c < 0.3: return f"(rd {inp} {s.atom(e())})"
        if inp and c < 0.45: return f"(len {inp})"
        if c < 0.6: return f"(bsize {s.atom(s.bufexpr(env, d, inp))})"
        if c < 0.8: return f"(bget {s.atom(s.bufexpr(env, d, inp))} {s.atom(e())})"
        return s.leaf(W, env, inp)
    def atom(s, x): return x if x.isdigit() or x.isidentifier() or x.startswith('(') and x.endswith(')') and x.count('(') == 1 else f"({x})"
    def bufexpr(s, env, d, inp):
        c = R.random()
        if c < 0.3: return 'bnew'
        vs = s.shapevars(env, W)
        if c < 0.75: return f"(bpush {s.atom(s.bufexpr(env, d-1, inp) if d > 0 else 'bnew')} {s.atom(s.expr(W, env, d-1, False, inp))})"
        return f"(bset {s.atom(s.bufexpr(env, d-1, inp) if d > 0 else 'bnew')} {R.randrange(0, 3)} {s.atom(s.expr(W, env, d-1, False, inp))})"
    def call(s, sh, env, d, inp):
        cs = [df for df in s.defs if df['res'] == sh and not df['loop']]
        lp = [df for df in s.defs if df['res'] == sh and df['loop']]
        if lp and R.random() < 0.4:
            df = R.choice(lp)
            fuel = R.choice([str(R.randrange(0, 50)), f"(len' {inp})" if inp else '3'])
            args = [fuel] + [s.argfor(p, env, d, inp) for p in df['params']]
            return "(" + df['name'] + " " + " ".join(a for a in args if a is not None) + ")"
        if not cs: return None
        df = R.choice(cs)
        args = [s.argfor(p, env, d, inp) for p in df['params']]
        return "(" + df['name'] + " " + " ".join(a for a in args if a is not None) + ")" if df['params'] else df['name']
    def argfor(s, p, env, d, inp):
        if p == 'inp': return inp if inp else 'x'
        return s.atom(s.expr(p, env, d-1, False, inp))
    def selfcall(s, env, d, inp):
        lc = s.loopctx
        args = [lc['n']] + [(inp if p == 'inp' else s.atom(s.expr(p, env, d-1, False, inp))) for p in lc['params']]
        return f"{lc['name']} " + " ".join(args)
def gen_program():
    g = G(); out = []
    for k in range(R.randrange(1, 5)):
        name = 'f' + str(k) + R.choice(['', 'a', ''])[:0]
        name = 'f' + str(k)
        loop = R.random() < 0.3
        res = rshape(1)
        ps = [(g.fresh(), rshape(1)) for _ in range(R.randrange(1 if loop else 0, 4))]
        useinp = R.random() < 0.4
        inp = 'z' + str(k) if useinp else None
        if not loop:
            if not ps and not useinp:
                body = g.expr(res, [], 2, False, None, True); out.append(f"def {name} : {sstr(res)} := {body}")
            else:
                env = [(n, t) for n, t in ps]
                body = g.expr(res, env, 4, False, inp, True)
                bs = ([f"({inp} : List UInt8)"] if useinp else []) + [f"({n} : {sstr(t)})" for n, t in ps]
                out.append(f"def {name} {' '.join(bs)} : {sstr(res)} := {body}")
            g.defs.append(dict(name=name, params=(['inp'] if useinp else []) + [t for n, t in ps], res=res, loop=False))
        else:
            n = g.fresh()
            names = [g.fresh() for _ in ps]
            tys = (['List UInt8'] if useinp else []) + [sstr(t) for n_, t in ps]
            sig = f"Nat → " + " → ".join(tys + [sstr(res)]) if tys else f"Nat → {sstr(res)}"
            env = [(nm, t) for nm, (_, t) in zip(names, ps)]
            pats = ([inp] if useinp else []) + names
            z = g.expr(res, env, 2, False, inp, True)
            g.loopctx = dict(name=name, n=n, params=(['inp'] if useinp else []) + [t for _, t in ps])
            sbody = g.expr(res, env, 4, True, inp, True)
            g.loopctx = None
            zp = ", ".join(["0"] + pats); sp = ", ".join([f"{n} + 1"] + pats)
            out.append(f"def {name} : {sig}\n  | {zp} => {z}\n  | {sp} => {sbody}")
            g.defs.append(dict(name=name, params=(['inp'] if useinp else []) + [t for _, t in ps], res=res, loop=True))
    # main: put the words of a few expressions
    body = '[]'
    for _ in range(R.randrange(1, 4)):
        body = f"put {g.atom(body)} {g.atom(g.expr(W, [], 3, False, 'x', True))}"
    out.append(f"def m (x : List UInt8) : List UInt8 := {body}")
    return "\n\n".join(out) + "\n"
POOL = ["+", "(", ")", ",", "n", "x", "0", "7", "let", "if", "then", "else", ":=", ";", "<<<", "==", "<", "def", "bnew", "rd", "len", "put", "f0", "f1", "|", "=>", "UInt64", "×", "→", "Nat", "[", "]", "≤", "&&", "a1"]
def mutate(src):
    toks = src.replace("\n", " \n ").split(" ")
    idx = [i for i, t in enumerate(toks) if t.strip() != ""]
    if not idx: return src
    i = R.choice(idx); c = R.random()
    if c < 0.3: toks.pop(i)
    elif c < 0.7: toks[i] = R.choice(POOL)
    elif c < 0.85: toks.insert(i, toks[i])
    else:
        j = R.choice(idx); toks[i], toks[j] = toks[j], toks[i]
    return " ".join(toks)
d, N = sys.argv[1], int(sys.argv[2]); os.makedirs(d, exist_ok=True)
for i in range(N):
    p = gen_program()
    if i % 2: p = mutate(p)
    open(f"{d}/p{i}.txt", "w").write(p)

# ---- tail-position cases (Astra 9/10 traps): exhaustive contexts around one self-call, valid and invalid, appended after the random ones
CTX = ["{c}", "({c})", "{c} + 1", "({c}) + 1", "1 + {c}", "1 + ({c})", "let q := {c}; q", "let q := 1; {c}", "if p < 3 then {c} else p",
       "if {c} < 3 then p else p", "if p < 3 then p else ({c})", "let q := 1; let r := q; (if q < r then {c} else r)",
       "g n ({c})", "h ({c})", "(if p < 3 then {c} else p) + 1", "let (u, v) := (p, 1); {c}", "let (u, v) := ({c}, 1); u"]
CALLS = ["g n (p + 1)", "g n p", "g p p", "g n", "g n p p", "g q (p + 1)", "g 0 p"]
k = N
for ctx in CTX:
    for call in CALLS:
        src = "def h (a : UInt64) : UInt64 := a\n\ndef g : Nat → UInt64 → UInt64\n  | 0, p => p\n  | n + 1, p => " + ctx.format(c=call) + "\n\ndef m (x : List UInt8) : List UInt8 := put [] (g 3 1)\n"
        open(f"{d}/p{k}.txt", "w").write(src); k += 1
print(k)
