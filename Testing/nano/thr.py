"""Resource limits of Lean's elaborator vs nano (maximum recursion depth etc.): per construct and size n, `L`/`l` = Lean accepts/rejects, `N`/`n` = nano
accepts/rejects.  Differences found: nano accepted >= 512 nested lets and chains of >= 3000 operands (Lean rejects): `nestOk`, `sizeOk` in Elab.lean."""
import json, os, subprocess, sys
ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
H = "def g (a : UInt64) : UInt64 := a + 1\ndef f (x : UInt64) : UInt64 := "
C = {
 "lets":    lambda n: H + "".join(f"let a := x + {i}; " for i in range(n)) + "a\n",
 "parens":  lambda n: H + "(" * n + "x" + ")" * n + "\n",
 "rparen":  lambda n: H + "x + (x * (" * (n // 2) + "x" + "))" * (n // 2) + "\n",
 "calls":   lambda n: H + "g (" * n + "x" + ")" * n + "\n",
 "letval":  lambda n: H + "(let a := " * n + "x; a" + ")" * n + "\n",
 "sum":     lambda n: H + " + ".join(["x"] * n) + "\n",
 "mulsub":  lambda n: H + "x" + "".join(" * 3 - 1" for _ in range(n // 2)) + "\n",
 "defs":    lambda n: "".join(f"def d{i} (x : UInt64) : UInt64 := " + (f"d{i-1} x + 1" if i else "x") + "\n" for i in range(n)) + f"def f (x : UInt64) : UInt64 := d{n-1} x\n",
 "params":  lambda n: "def f (" + " ".join(f"p{i}" for i in range(n)) + " : UInt64) : UInt64 := p0\n",
 "digits":  lambda n: H + "1" + "0" * n + "\n",
}
def run(items):
    cases = [dict(src=s, name="f", ty="UInt64", ins=[["1"] * k for _ in range(2)]) for s, k in items]
    inp = "\n".join(json.dumps(c) for c in cases) + "\n"
    out = subprocess.run("ulimit -s unlimited; PATH=$HOME/.elan/bin:$PATH lake env lean --tstack=4000000 --run Testing/nano/oracle.lean", shell=True, input=inp, capture_output=True, text=True, cwd=ROOT)
    res = []
    for l in out.stdout.splitlines():
        r, n = l.split(" nano="); res.append((r[5:] != "R", n != "R"))
    assert len(res) == len(items), out.stderr[-500:]
    return res
which = sys.argv[1:] or list(C)
for k in which:
    ns = [100, 1000, 3000, 10000, 20000, 50000] if k in ("sum", "mulsub", "digits") else [100, 500, 1000, 2000, 5000]
    ar = lambda n: n if k == "params" else 1
    res = run([(C[k](n), ar(n)) for n in ns])
    print(k, " ".join(f"{n}:{'L' if a else 'l'}{'N' if b else 'n'}" for n, (a, b) in zip(ns, res)), flush=True)
