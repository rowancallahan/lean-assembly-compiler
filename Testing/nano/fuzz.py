#!/usr/bin/env python3
"""(5) fuzz: random nano programs are elaborated by Lean (real `def`s, evaluated by the interpreter) and by nanoElab
(+ Prog.eval); outputs on random inputs compared.  Also: invalid programs must be rejected by nanoElab AND fail in Lean.
usage: fuzz.py [N programs] [seed]"""
import os, random, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nanolib import *
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "work"); ROOT = os.path.abspath(os.path.join(D, "..", ".."))
os.makedirs(W, exist_ok=True)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 7); g = G(rng)
progs = [g.program() for _ in range(N)]
lit = lambda s: '"' + s.replace("\\", "\\\\").replace("\n", "\\n") + '"'
L = ["import Legacy.Nano.Gen", "open Nano", "set_option linter.unusedVariables false", ""]
calls = []
for i, s in enumerate(progs):
    k = entry_arity(s); name = re.findall(r"^def\s+(\w+)", s, re.M)[-1]
    L += [f"namespace Q{i}", s, "end Q" + str(i)]
    ins = inputs(rng, k, 8)
    calls.append((i, name, ins))
L += ["def chk (src : String) (real : List UInt64 → UInt64) (ins : List (List UInt64)) : IO (Nat × Nat) := do",
      "  let mut ok := 0; let mut bad := 0",
      "  for a in ins do",
      "    if (nanoElab src.toUTF8.toList).bind (·.eval a) == some (real a) then ok := ok + 1",
      "    else bad := bad + 1; IO.println s!\"MISMATCH {src} {a}\"",
      "  return (ok, bad)",
      ""]
for (i, name, ins) in calls:
    k = len(ins[0])
    real = "fun a => " + f"Q{i}.{name} " + " ".join(f"(a.getD {j} 0)" for j in range(k))
    L += [f"def t{i} : IO (Nat × Nat) := chk {lit(progs[i])} ({real}) {ins}"]
for c in range(0, N, 20):
    L += [f"def chunk{c // 20} : List (IO (Nat × Nat)) := [" + ", ".join(f"t{i}" for i in range(c, min(N, c + 20))) + "]"]
L += ["def main : IO Unit := do", "  let mut ok := 0; let mut bad := 0"]
for c in range(0, N, 20):
    L += [f"  for t in chunk{c // 20} do", "    let r ← t", "    ok := ok + r.1; bad := bad + r.2"]
L += ["  IO.println s!\"programs: " + str(N) + " input vectors ok: {ok} mismatches: {bad}\"", "  if bad != 0 then throw (IO.userError \"MISMATCH\")"]
open(f"{W}/fuzz.lean", "w").write("\n".join(L) + "\n")
r = subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH lake env lean --run {W}/fuzz.lean", shell=True, capture_output=True, text=True)
print(r.stdout[-2000:], r.stderr[-3000:] if r.returncode else "")
assert r.returncode == 0
# negatives: nanoElab rejects, and Lean rejects too
for s in NEG:
    open(f"{W}/neg.lean", "w").write(s + "\n")
    lean = subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH lake env lean {W}/neg.lean", shell=True, capture_output=True, text=True)
    open(f"{W}/neg.nano", "w").write(s)
    nano = subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH lake env lean --run Testing/nano/show.lean {W}/neg.nano", shell=True, capture_output=True, text=True).stdout.strip()
    print(f"negative {s!r}: Lean {'rejects' if lean.returncode else 'ACCEPTS'}, nanoElab {nano[:6]}")
    assert nano == "NONE"
