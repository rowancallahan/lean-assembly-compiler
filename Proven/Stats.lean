/- Instruction counts by category for the standard and fast backends: [const, move, op, select, return].
   The generated code is straight-line (no branches), so words = instructions executed per call. -/
import Proven.CompilerArm
import Proven.CodeFast
import Proven.CompilerArmFast
namespace Proven.Stats
open Proven

def add (a b : List Nat) : List Nat := a.zipWith (· + ·) b
def one (i n : Nat) : List Nat := (List.replicate 5 0).mapIdx fun j _ => if j = i then n else 0

/-- standard RV64 backend (`Proven.compile`) -/
def rvStd : Exp → List Nat
  | .var _ => one 1 1
  | .const c => one 0 (genConst 0 c.toNat).length
  | .bin op a b => add (add (rvStd a) (rvStd b)) (one 2 (opCode op 0).length)
  | .ite c a b => add (add (rvStd c) (add (rvStd a) (rvStd b))) (one 3 (selCode 0).length)
/-- standard AArch64 backend (`Proven.Arm.compile`) -/
def armStd : Exp → List Nat
  | .var _ => one 1 1
  | .const c => one 0 (Arm.genConst 0 c.toNat).length
  | .bin op a b => add (add (armStd a) (armStd b)) (one 2 (Arm.opCode op 0).length)
  | .ite c a b => add (add (armStd c) (add (armStd a) (armStd b))) (one 3 (Arm.selCode 0).length)

def fin (l : List Nat) : List Nat := add l (add (one 1 1) (one 4 1))
def tagged (l : List Fast.W) : List Nat := l.foldl (fun acc w => add acc (one w.1 1)) (List.replicate 5 0)

def of (backend : String) (e : Exp) : List Nat :=
  match backend with
  | "rv-std" => fin (rvStd e)
  | "arm-std" => fin (armStd e)
  | "rv-fast" => tagged (Fast.compileT e)
  | _ => tagged (Arm.Fast.compileT e)

/-- print a table for a corpus of expressions -/
def report (name : String) (es : List Exp) : IO Unit := do
  IO.println s!"corpus {name}: {es.length} expressions"
  IO.println "  backend    words/expr  const  move    op   select  return   (sum of words over corpus; avg words per expr)"
  for b in ["rv-std", "rv-fast", "arm-std", "arm-fast"] do
    let t := es.foldl (fun acc e => add acc (of b e)) (List.replicate 5 0)
    let tot := t.foldl (· + ·) 0
    let a := tot * 100 / es.length
    IO.println s!"  {b}  avg {a / 100}.{if a % 100 < 10 then "0" else ""}{a % 100}  {t}  total {tot}"
end Proven.Stats
