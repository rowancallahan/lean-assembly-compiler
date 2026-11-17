import Nano.V2.Copy
/- nano v2 small backend: words and cases for Testing/nano/v2_test.py (Testing/asm/ir-words/nv2_*, gitignored).
cases line: input hex, status, expected output hex ("-" = empty). Expected = `Prog.eval` (the backend's meaning),
checked equal to the ordinary-Lean `copyLean`. -/
open Nano.V2
def hex (l : List UInt8) : String :=
  if l.isEmpty then "-" else String.join (l.map fun b => let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length = 1 then "0" ++ s else s)
def hex8 (w : UInt32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def rnd (seed n : Nat) : List UInt8 := (List.range n).map fun k => ((seed * 1103515245 + k * 12345 + k * k * 7) % 256).toUInt8
def inputs : List (List UInt8) :=
  [[0, 127, 128, 255], [], [1, 2, 3, 4, 5], [7], [255, 255]] ++ (List.range 12).map (fun k => rnd k (3 * k + 1)) ++
  [rnd 99 99, rnd 100 100, rnd 101 101]
def progs : List (String × Prog × Option (List UInt8 → Except UInt64 (List UInt8))) :=
  [("nv2_copy", copyProg 100 100, some (copyLean 100 100)), ("nv2_copyfuel", copyProg 3 100, some (copyLean 3 100)),
   ("nv2_copycap", copyProg 100 3, some (copyLean 100 3)), ("nv2_mix", mixProg, none)]
def main : IO Unit := do
  for (nm, p, ref) in progs do
    let some ws := gen p | throw (IO.userError s!"{nm}: gen failed")
    IO.FS.writeFile s!"Testing/asm/ir-words/{nm}.words" (s!"{nm} 1\n" ++ String.join (ws.map fun w => hex8 w ++ "\n"))
    let mut cs := ""
    for x in inputs do
      let e := p.eval x
      if let some f := ref then
        if toString (repr e) != toString (repr (f x)) then throw (IO.userError s!"{nm}: Prog.eval ≠ copyLean")
      match e with
      | .ok y => cs := cs ++ s!"{hex x} 0 {hex y}\n"
      | .error s => cs := cs ++ s!"{hex x} {s} -\n"
    IO.FS.writeFile s!"Testing/asm/ir-words/{nm}.cases" cs
    IO.println s!"{nm}: {ws.length} words, {inputs.length} cases"
