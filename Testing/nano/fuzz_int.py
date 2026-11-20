#!/usr/bin/env python3
"""Int64 fuzz: random nano programs over Int64 (and over UInt64, both with negative numerals) are elaborated by Lean (real
`def`s, run by the interpreter) and by nanoElabT (+ Prog.evalI / Prog.eval); outputs on random signed/edge inputs compared,
and the type found by nanoElabT must be the program's.  Then INT_NEG: nanoElab rejects each; Lean's verdict printed.
usage: fuzz_int.py [N Int64 programs] [seed] [M UInt64 programs]"""
import os, random, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nanolib import *
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "work"); ROOT = os.path.abspath(os.path.join(D, "..", ".."))
os.makedirs(W, exist_ok=True)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 11)
NU = int(sys.argv[3]) if len(sys.argv) > 3 else 50
gi, gu = GI(rng, "Int64"), GI(rng, "UInt64")
progs = [("Int64", gi.program()) for _ in range(N)] + [("UInt64", gu.program()) for _ in range(NU)]
lit = lambda s: '"' + s.replace("\\", "\\\\").replace("\n", "\\n") + '"'
L = ["import Legacy.Nano.Int", "import Legacy.Nano.Elab", "open Nano", "set_option linter.unusedVariables false", "set_option maxRecDepth 10000", ""]
for i, (T, s) in enumerate(progs): L += [f"namespace Q{i}", s, f"end Q{i}"]
L += ["def chkI (src : String) (real : List Int64 → Int64) (ins : List (List Int64)) : IO (Nat × Nat) := do",
      "  let mut ok := 0; let mut bad := 0",
      "  for a in ins do",
      "    if (nanoElabT src.toUTF8.toList).bind (fun r => if r.1 then r.2.evalI a else none) == some (real a) then ok := ok + 1",
      "    else bad := bad + 1; IO.println s!\"MISMATCH {src} {a}\"",
      "  return (ok, bad)",
      "def chkU (src : String) (real : List UInt64 → UInt64) (ins : List (List UInt64)) : IO (Nat × Nat) := do",
      "  let mut ok := 0; let mut bad := 0",
      "  for a in ins do",
      "    if (nanoElabT src.toUTF8.toList).bind (fun r => if r.1 then none else r.2.eval a) == some (real a) then ok := ok + 1",
      "    else bad := bad + 1; IO.println s!\"MISMATCH {src} {a}\"",
      "  return (ok, bad)", ""]
for i, (T, s) in enumerate(progs):
    k = entry_arity(s); name = re.findall(r"^def\s+(\w+)", s, re.M)[-1]
    ins = inputs_i(rng, k, 8) if T == "Int64" else [[a % M for a in v] for v in inputs_i(rng, k, 8)]
    real = "fun a => " + f"Q{i}.{name} " + " ".join(f"(a.getD {j} 0)" for j in range(k))
    L += [f"def t{i} : IO (Nat × Nat) := {'chkI' if T == 'Int64' else 'chkU'} {lit(s)} ({real}) {ins}"]
n = len(progs)
for c in range(0, n, 20):
    L += [f"def chunk{c // 20} : List (IO (Nat × Nat)) := [" + ", ".join(f"t{i}" for i in range(c, min(n, c + 20))) + "]"]
L += ["def fuzzMain : IO Unit := do", "  let mut ok := 0; let mut bad := 0"]
for c in range(0, n, 20):
    L += [f"  for t in chunk{c // 20} do", "    let r ← t", "    ok := ok + r.1; bad := bad + r.2"]
L += ["  IO.println s!\"programs: " + f"{N} Int64 + {NU} UInt64" + " input vectors ok: {ok} mismatches: {bad}\"",
      "  if bad != 0 then throw (IO.userError \"MISMATCH\")", "#eval fuzzMain"]
open(f"{W}/fuzz_int.lean", "w").write("\n".join(L) + "\n")
r = subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH lake env lean {W}/fuzz_int.lean", shell=True, capture_output=True, text=True)
print(r.stdout[-2000:], r.stderr[-3000:] if r.returncode else "")
assert r.returncode == 0
for s in INT_NEG:
    open(f"{W}/neg.lean", "w").write(s + "\n")
    lean = subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH lake env lean {W}/neg.lean", shell=True, capture_output=True, text=True)
    open(f"{W}/neg.nano", "w").write(s)
    nano = subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH lake env lean --run Testing/nano/show.lean {W}/neg.nano", shell=True, capture_output=True, text=True).stdout.strip()
    print(f"negative {s!r}: Lean {'rejects' if lean.returncode else 'ACCEPTS'}, nanoElab {nano[:6]}")
    assert nano == "NONE"
