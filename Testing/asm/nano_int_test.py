#!/usr/bin/env python3
"""Int64 nano programs through the proved generator `nanoGenIR` (= code of `nanoCompileIR`, Nano/ProofTop.lean) on QEMU and
on the Sail C simulator: Testing/nano/nanolib.INT_CORPUS + R random Int64 programs (GI), 8 signed / overflow / edge input
vectors each.  The Lean emitter (generated: Testing/nano/work/emit_int.lean) elaborates with nanoElabT (type must be
Int64), writes `nanoGenIR p` words and per case input = `encIs args`, expected = `nanoRun p input`, and CHECKS
expected = `encI (f args)` with `f` Lean's own `def` of the same text (and words == Ir.compileW).  Then
Testing/asm/ir_test.py check 8 nano_i64_<i> (memoryNeeded and memoryNeeded - 1).  Removes Testing/asm/ctest.
usage: nano_int_test.py [R random programs] [seed]"""
import os, random, re, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Testing", "nano"))
from nanolib import *
R = int(sys.argv[1]) if len(sys.argv) > 1 else 12
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 5); g = GI(rng, "Int64")
progs = list(INT_CORPUS) + [g.program() for _ in range(R)]
lit = lambda s: '"' + s.replace("\\", "\\\\").replace("\n", "\\n") + '"'
L = ["import Nano.ProofTop", "import Nano.Int", "import Nano.Elab", "open Proven (leN)", "open Proven.Ir Proven.Top.Alloc Nano",
     "set_option linter.unusedVariables false", "set_option maxRecDepth 10000",
     "def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then \"0\" ++ s else s",
     "def hx (xs : List UInt8) : String := if xs.isEmpty then \"-\" else String.join (xs.map hex2)",
     "def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); \"\".pushn '0' (8 - s.length) ++ s",
     "def mainSlots (Q : Proven.Ir.Prog Nat) : Nat := ((Q.funcs[Q.main]?).map (·.slots)).getD 0",
     "def peakF (E : List MemEvent) : Nat :=",
     "  (E.reverse.foldl (fun (c, m) e => match e with",
     "    | .alloc n => (c + n, max m (c + n)) | .free n => (c - n, max m (c - n))) (0, 0)).2",
     "def emitI (name src : String) (real : List Int64 → Int64) (ins : List (List Int64)) : IO Unit := do",
     "  match nanoElabT src.toUTF8.toList with",
     "  | some (true, p) =>",
     "    match compileW (lower p) with",
     "    | none => throw (IO.userError s!\"{name}: compile failed\")",
     "    | some (ws, Q) =>",
     "      unless Proven.Top.wordBytes ws == nanoGenIR p do throw (IO.userError s!\"{name}: WORDS != nanoGen\")",
     "      IO.FS.writeFile s!\"Testing/asm/ir-words/{name}.words\" (String.intercalate \"\\n\" (s!\"{name} 0\" :: ws.map hex8) ++ \"\\n\")",
     "      let mut s := \"\"",
     "      for args in ins do",
     "        let x := encIs args",
     "        match nanoRun p x, interp Q 100000000 x with",
     "        | some y, some (o, ev) =>",
     "          unless y == encI (real args) do throw (IO.userError s!\"{name}: nanoRun != Lean def {args}\")",
     "          unless o == y do throw (IO.userError s!\"{name}: interpreter != nanoRun\")",
     "          s := s ++ s!\"{hx x} {hx y} {8 * peakF (ev ++ [.alloc (mainSlots Q + 3)])}\\n\"",
     "        | _, _ => throw (IO.userError s!\"{name}: no result\")",
     "      IO.FS.writeFile s!\"Testing/asm/ir-words/{name}.cases\" s",
     "      IO.println s!\"{name}: arity {p.1}, {ws.length} words\"",
     "  | _ => throw (IO.userError s!\"{name}: nanoElabT did not give an Int64 program\")", ""]
body = ["def runAll : IO Unit := do"]
for i, s in enumerate(progs):
    k = entry_arity(s); name = re.findall(r"^def\s+(\w+)", s, re.M)[-1]
    L += [f"namespace Q{i}", s, f"end Q{i}"]
    ins = inputs_i(rng, k, 8)
    real = "fun a => " + f"Q{i}.{name} " + " ".join(f"(a.getD {j} 0)" for j in range(k))
    body.append(f"  emitI \"nano_i64_{i}\" {lit(s)} ({real}) {ins}")
os.makedirs(os.path.join(ROOT, "Testing", "nano", "work"), exist_ok=True)
os.makedirs(os.path.join(D, "ir-words"), exist_ok=True)
EF = os.path.join(ROOT, "Testing", "nano", "work", "emit_int.lean")
open(EF, "w").write("\n".join(L + body + ["#eval runAll", ""]))
subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH lake env lean {EF}", shell=True, check=True)
n = 0
try:
    for i in range(len(progs)):
        subprocess.run(f"cd {ROOT} && python3 Testing/asm/ir_test.py check 8 nano_i64_{i}", shell=True, check=True); n += 8
finally:
    subprocess.run(f"rm -rf {D}/ctest", shell=True)
print(f"nano Int64: {len(progs)} programs, {n} program x input pairs ok on QEMU + Sail (== Lean's Int64 defs)")
