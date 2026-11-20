#!/usr/bin/env python3
"""nano v2 front end (increment 3: products + I/O prelude), oracle agreement fuzz.
Generates N random programs (seed S) in the accepted subset, runs
  (1) Lean itself on prelude + program (`#eval` over the inputs), the ORACLE;
  (2) `frontElabK 64` + `Prog.eval` (Testing/nano/v2f/run.lean);
and asserts: every program is accepted by nano and the outputs are identical.  With EMIT=1 also writes
Testing/asm/ir-words/nv2f_*.words/.cases for Testing/nano/v2b_test.py (QEMU + Sail).
usage: fuzz.py N SEED      (from the repo root; needs the Nano.V2.Front/Gen oleans: lake build Nano.V2.Front Nano.V2.Gen)
Also runs the hand cases Testing/nano/v2f/p*.lean and the negative cases Testing/nano/v2f/neg*.lean (nano must reject)."""
import os, random, subprocess, sys, glob
LEAN = os.environ.get("LEANCMD", "lake env lean").split()
R = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(R, "..", "..", "..")
W = os.path.join(ROOT, "Testing", "nano", "work", "v2f"); os.makedirs(W, exist_ok=True)
N, SEED = int(sys.argv[1]), int(sys.argv[2])
rng = random.Random(SEED)
PRE = open(os.path.join(R, "Prelude.lean.txt")).read()
INS = [[], [1], [5, 7, 9], [200, 100, 50, 25], [255, 0, 255, 3, 4], [9] * 12] + \
      [[rng.randrange(256) for _ in range(rng.randrange(1, 9))] for _ in range(6)]

U, P2, P3 = "UInt64", "UInt64 × UInt64", "UInt64 × (UInt64 × UInt64)"
TY = {U: "w", P2: ("w", "w"), P3: ("w", ("w", "w"))}

class G:
    def __init__(s): s.defs = []  # (name, [param types], result type)
    def var(s, env, t):
        c = [n for n, ty in env if ty == t]
        return rng.choice(c) if c else None
    def wleaf(s, env):
        """a TYPED word leaf"""
        opts = ["rd x ({})".format(s.small(env)), "len x"]
        v = s.var(env, "w")
        if v: opts += [v] * 3
        for n, ty in env:
            if ty == ("w", "w"): opts += [n + ".1", n + ".2"]
            if ty == ("w", ("w", "w")): opts += [n + ".1", n + ".2.1", n + ".2.2"]
        return rng.choice(opts)
    def small(s, env):
        v = s.var(env, "w")
        return (v + " &&& 7") if v and rng.random() < .5 else str(rng.randrange(8))
    def w(s, env, d):
        """a typed word expression (contains a typed leaf)"""
        if d <= 0: return s.wleaf(env)
        k = rng.randrange(8)
        if k == 0:
            return "{} {} {}".format(s.wleaf(env), rng.choice(["+", "-", "*", "&&&", "|||", "^^^"]),
                                     rng.choice([str(rng.randrange(1 << rng.choice([3, 20, 63]))), s.wleaf(env)]))
        if k == 1:
            return "({}) {} ({})".format(s.w(env, d - 1), rng.choice(["+", "-", "*", "^^^"]), s.w(env, d - 1))
        if k == 3:
            return "(if {} {} {} then {} else {})".format(s.w(env, d - 1), rng.choice(["<", "<=", "=="]),
                                                         s.w(env, d - 1), s.w(env, d - 1), s.w(env, d - 1))
        if k == 4:
            fs = [f for f in s.defs if f[2] == U]
            if fs:
                f = rng.choice(fs)
                return "({} {})".format(f[0], " ".join(s.arg(env, U if t == "U0" else t, d - 1) for t in f[1]))
        if k == 5:
            p = s.p(env, rng.choice([P2, P3]), d - 1)
            return "({}).{}".format(p, rng.choice(["1", "2.1"] if p.count(",") > 1 and False else ["1"]))
        return s.wleaf(env)
    def arg(s, env, t, d):
        return "({})".format(s.w(env, d)) if t == U else s.p(env, t, d)
    def p(s, env, t, d):
        """a product of type t, as an atom"""
        v = s.var(env, TY[t])
        k = rng.randrange(4)
        if v and k == 0: return v
        fs = [f for f in s.defs if f[2] == t]
        if fs and k == 1:
            f = rng.choice(fs)
            return "({} {})".format(f[0], " ".join(s.arg(env, U if a == "U0" else a, d - 1) for a in f[1]))
        if t == P2: return "({}, {})".format(s.w(env, d), s.w(env, d))
        return "({}, {}, {})".format(s.w(env, d), s.w(env, d), s.w(env, d))
    def body(s, env, t, d, n):
        """`let` chains (plain and destructuring), then a value of type t"""
        lines, env = [], list(env)
        for i in range(rng.randrange(3)):
            nm = "v{}_{}".format(n, i)
            k = rng.randrange(4)
            if k == 3:
                # shifts only alone in a `let` (the conservative SHIFT GUARD rejects a shift next to a numeral)
                v = s.var(env, "w") or "len x"
                lines.append("let {} := {} {} {};".format(nm, v, rng.choice(["<<<", ">>>"]), rng.randrange(64)))
                env.append((nm, "w"))
            elif k == 0: lines.append("let {} := {};".format(nm, s.w(env, d))); env.append((nm, "w"))
            elif k == 1:
                tt = rng.choice([P2, P3]); lines.append("let {} := {};".format(nm, s.p(env, tt, d))); env.append((nm, TY[tt]))
            else:
                a, b = nm + "_1", nm + "_2"
                lines.append("let ({}, {}) := {};".format(a, b, s.p(env, P2, d))); env += [(a, "w"), (b, "w")]
        return lines, (s.w(env, d) if t == U else s.p(env, t, d)), env
    def loop(s, i):
        """a fuel loop over the input with state (i, a : T)"""
        t = rng.choice([U, P2, P3])
        env = [("x", None), ("i", "w"), ("a", TY[t])]
        stop = s.p(env, t, 1) if t != U else s.w(env, 1)
        nxt = s.p(env + [("v", "w")], t, 1) if t != U else s.w(env + [("v", "w")], 1)
        z = s.p(env, t, 1) if t != U else s.w(env, 1)
        src = ("def l{0} : Nat → List UInt8 → UInt64 → {1} → {1}\n  | 0, x, i, a => {2}\n"
               "  | n + 1, x, i, a =>\n    if len x <= i then {3} else\n    let v := rd x i;\n    l{0} n x (i + 1) ({4})\n"
               ).format(i, t, z, stop, nxt)
        s.defs.append(("l{} (len' x + {}) x".format(i, rng.randrange(3)), ["U0"] + [t], t))
        return src
    def helper(s, i):
        if rng.random() < .35: return s.loop(i)
        ps = [rng.choice([U, U, P2, P3]) for _ in range(rng.randrange(1, 4))]
        rt = rng.choice([U, P2, P3])
        names = ["a{}".format(j) for j in range(len(ps))]
        env = [(n, TY[t]) for n, t in zip(names, ps)]
        lines, e, _ = s.body([("x", None)] + env, rt, 2, i)
        src = "def f{} (x : List UInt8) {} : {} :=\n  {}\n".format(
            i, " ".join("({} : {})".format(n, t) for n, t in zip(names, ps)), rt, "\n  ".join(lines + [e]))
        s.defs.append(("f{} x".format(i), ps, rt))
        return src
    def main(s):
        lines, e, env = s.body([], U, 2, 99)
        puts = [s.w(env, 2) for _ in range(rng.randrange(1, 4))]
        o = "[]"
        for q in [e] + puts: o = "put ({}) ({})".format(o, q)
        if rng.random() < .3:
            o = "if {} < {} then {} else put [] ({})".format(s.w(env, 1), s.w(env, 1), o, s.w(env, 1))
        return "def m (x : List UInt8) : List UInt8 :=\n  {}\n".format("\n  ".join(lines + [o]))

def prog(i):
    g = G()
    return "".join(g.helper(j) for j in range(rng.randrange(3))) + g.main()

hexs = lambda l: "".join("%02x" % b for b in l) or "-"
open(os.path.join(W, "inputs.txt"), "w").write("".join(hexs(x) + "\n" for x in INS))
files = sorted(glob.glob(os.path.join(R, "p*.lean")))
for i in range(N):
    f = os.path.join(W, "g%04d.lean" % i); open(f, "w").write(prog(i)); files.append(f)
# (1) the oracle
orc = "set_option linter.unusedVariables false\n" + PRE + "def ins : List (List UInt8) := %s\n" % repr(INS).replace(" ", "")
names = []
for f in files:
    nm = os.path.basename(f)[:-5]; names.append(nm)
    orc += "namespace N%s\n%s\nend N%s\n" % (nm, open(f).read(), nm)
    orc += '#eval ins.zipIdx.forM fun (x, i) => IO.println s!"%s {i} {N%s.m x}"\n' % (nm, nm)
open(os.path.join(W, "oracle.lean"), "w").write(orc)
o = subprocess.run(LEAN + [os.path.join(W, "oracle.lean")], cwd=ROOT, capture_output=True, text=True)
assert o.returncode == 0, o.stdout[-3000:] + o.stderr[-3000:]
def lst(s): return [int(t) for t in s.strip("[]").split(",") if t.strip()]
exp = {}
import re
for l in o.stdout.splitlines():
    if not re.match(r"^\S+ \d+ \[", l): continue
    nm, i, rest = l.split(" ", 2)
    y = lst(rest); exp[(nm, int(i))] = "E1" if not y else hexs(y)
# (2) nano
out = os.path.join(ROOT, "Testing", "asm", "ir-words") if os.environ.get("EMIT") else "-"
n = subprocess.run(LEAN + ["--run", os.path.join(R, "run.lean"), os.path.join(W, "inputs.txt"), out] + files,
                   cwd=ROOT, capture_output=True, text=True)
assert n.returncode == 0, n.stderr[-3000:]
got, rej = {}, []
for l in n.stdout.splitlines():
    p = l.split()
    if p[1] == "REJECT": rej.append(p[0])
    else: got[(p[0], int(p[1]))] = p[2]
assert not rej, "nano rejected: %s" % rej
bad = [(k, exp[k], got.get(k)) for k in exp if exp[k] != got.get(k)]
assert not bad, bad[:10]
# negative cases: nano must reject
neg = sorted(glob.glob(os.path.join(R, "neg*.lean")))
if neg:
    n = subprocess.run(LEAN + ["--run", os.path.join(R, "run.lean"), os.path.join(W, "inputs.txt"), "-"] + neg,
                       cwd=ROOT, capture_output=True, text=True)
    acc = sorted({l.split()[0] for l in n.stdout.splitlines() if l.split()[1] != "REJECT"})
    assert not acc, "nano accepted negative cases: %s" % acc
print("v2f fuzz: %d programs x %d inputs agree with Lean; %d negative cases rejected" % (len(files), len(INS), len(neg)))
