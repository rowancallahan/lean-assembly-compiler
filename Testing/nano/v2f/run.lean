import Legacy.Nano.V2.Front
import Nano.Base.V2.Gen
/- nano v2 front end test runner: `lake env lean --run Testing/nano/v2f/run.lean INPUTS OUTDIR? FILE...`
Per FILE: `frontElabK 64`; prints `name REJECT` or `name i hex` per input (hex of the output, `E<status>` on error);
with OUTDIR ≠ "-": writes OUTDIR/nv2f_<name>.words/.cases for Testing/nano/v2b_test.py. -/
open Nano.V2B
def hex (l : List UInt8) : String :=
  if l.isEmpty then "-" else String.join (l.map fun b => let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length = 1 then "0" ++ s else s)
def hex8 (w : UInt32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hexv (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
def unhex' (s : String) : List UInt8 :=
  if s = "-" then [] else
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i => (hexv cs[2*i]! * 16 + hexv cs[2*i+1]!).toUInt8
def main (args : List String) : IO Unit := do
  let ins := ((← IO.FS.readFile args[0]!).splitOn "\n").filter (· ≠ "") |>.map unhex'
  let out := args[1]!
  for f in args.drop 2 do
    let nm := ((f.splitOn "/").getLast!.splitOn ".")[0]!
    match frontElabK 64 (← IO.FS.readFile f).toUTF8.toList with
    | none => IO.println s!"{nm} REJECT"
    | some p =>
      let mut cs := ""
      for (x, i) in ins.zipIdx do
        match p.eval x with
        | .ok y => IO.println s!"{nm} {i} {hex y}"; cs := cs ++ s!"{hex x} 0 {hex y}\n"
        | .error s => IO.println s!"{nm} {i} E{s}"; cs := cs ++ s!"{hex x} {s} -\n"
      if out != "-" then
        let some ws := gen p | throw (IO.userError s!"{nm}: gen failed")
        IO.FS.writeFile s!"{out}/nv2f_{nm}.words" (s!"nv2f_{nm} 1\n" ++ String.join (ws.map fun w => hex8 w ++ "\n"))
        IO.FS.writeFile s!"{out}/nv2f_{nm}.cases" cs
