"""Resource limits of Lean's elaborator vs nano (maximum recursion depth etc.): per construct and size n, `L`/`l` = Lean accepts/rejects, `N`/`n` = nano
accepts/rejects.  Differences found: nano accepted >= 512 nested lets and chains of >= 3000 operands (Lean rejects): `nestOk`, `sizeOk` in Elab.lean."""
import json, os, subprocess, sys
ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
def mk(n):  # def g with n params, called with n args in f
    return "def g (" + " ".join(f"p{i}" for i in range(n)) + " : UInt64) : UInt64 := p0 + p1\ndef f (x : UInt64) : UInt64 := g" + " x" * n + "\n"
def mk2(n):  # n defs each with 3 lets and sums
    return "".join(f"def d{i} (x : UInt64) : UInt64 := let a := x + 1; let b := a * 2; " + (f"d{i-1} b" if i else "b") + " + a\n" for i in range(n)) + f"def f (x : UInt64) : UInt64 := d{n-1} x\n"
def mk3(n):  # one def, n lets each with a sum of 10
    return "def f (x : UInt64) : UInt64 := " + "".join(f"let a := x + x + x + x + x + x + x + x + x + {i}; " for i in range(n)) + "a\n"
def mk4(n):  # n-ary call nest: g2 (g2 x x) (g2 ...) balanced? depth log; use right comb of sums of calls
    return "def g (a b : UInt64) : UInt64 := a + b\ndef f (x : UInt64) : UInt64 := " + " + ".join(["g x x"] * n) + "\n"
for name, fn, ns in [("bigcall", mk, [100, 300, 500, 1000, 2000]), ("defs3", mk2, [100, 300, 1000]), ("lets10", mk3, [20, 50, 100, 200]), ("callsum", mk4, [100, 500, 1000, 2000])]:
    cases = [dict(src=fn(n), name="f", ty="UInt64", ins=[["1"], ["2"]]) for n in ns]
    out = subprocess.run("ulimit -s unlimited; PATH=$HOME/.elan/bin:$PATH lake env lean --tstack=4000000 --run Testing/nano/oracle.lean", shell=True, input="\n".join(json.dumps(c) for c in cases) + "\n", capture_output=True, text=True, cwd=ROOT)
    r = [(l.split(" nano=")[0][5:] != "R", l.split(" nano=")[1] != "R") for l in out.stdout.splitlines()]
    print(name, " ".join(f"{n}:{'L' if a else 'l'}{'N' if b else 'n'}" for n, (a, b) in zip(ns, r)), flush=True)
