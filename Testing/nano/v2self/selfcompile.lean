import Legacy.Nano.V2.Front
import Nano.Base.V2.Gen
/- `lean --run selfcompile.lean KAPPA OUTDIR FILE...`: strip + concatenate FILEs (as check.lean), compile with
`frontElabK KAPPA` + `gen`; writes OUTDIR/src.txt (the text = program input) and OUTDIR/P.words (hex words, v2b format). -/
open Nano.V2B
def strip (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut inC := false
  for l in s.splitOn "\n" do
    if inC then
      if (l.splitOn "-/").length > 1 then inC := false
    else if l.startsWith "/-" then
      if (l.splitOn "-/").length ≤ 1 then inC := true
    else if l.startsWith "import" || l.startsWith "--" || l.startsWith "namespace" || l.startsWith "end " then pure ()
    else out := out ++ [l]
  return out
def hex8 (w : UInt32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def main (args : List String) : IO Unit := do
  let κ := args[0]!.toNat!
  let mut txt := ""
  for f in args.drop 2 do txt := txt ++ "\n".intercalate (strip (← IO.FS.readFile f)) ++ "\n"
  IO.FS.writeFile s!"{args[1]!}/src.txt" txt
  IO.println s!"source: {txt.utf8ByteSize} bytes"
  let some p := frontElabK κ txt.toUTF8.toList | throw (IO.userError "front end REJECTED the source")
  IO.println "front end accepted"
  let some ws := gen p | throw (IO.userError "gen failed")
  IO.println s!"P: {ws.length} words = {4 * ws.length} bytes"
  IO.FS.writeFile s!"{args[1]!}/P.words" ("selfcompile 1\n" ++ String.join (ws.map fun w => hex8 w ++ "\n"))
