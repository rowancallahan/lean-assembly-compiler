/- differential test: the reference grammar (Nano/V2Self/Proof/ParSpec.lean) against Par1.  usage:
   B1 parse < self_S_input.txt > ast.bin   (B1 from boot/build_B1.py, `parse` mode)
   lake env lean --tstack=1000000 --run Testing/nano/v2self/parspec_diff.lean self_S_input.txt ast.bin
   prints whether serialize (refParse (lex src)) equals Par1's word stream (result 2026-11-18: 190 defs, 27,979 words, equal). -/
import Nano.V2Self.Proof.ParSpec
open ParSpec
def readWords (p : String) : IO (List UInt64) := do
  let b ← IO.FS.readBinFile p
  let n := b.size / 8
  return (List.range n).map fun i => (List.range 8).foldl (fun a j => a ||| ((b.get! (8*i+j)).toUInt64 <<< (8*j).toUInt64)) 0
def main (args : List String) : IO Unit := do
  let src ← IO.FS.readBinFile args[0]!
  let exp ← readWords args[1]!
  match lexAll (src.size + 1) src.toList with
  | none => IO.println "lex failed"
  | some ts =>
    IO.println s!"tokens {ts.length}"
    match refParse ts with
    | none => IO.println "refParse REJECTED"
    | some p =>
      let got := serialize p
      IO.println s!"spec words {got.length}, par1 words {exp.length}, equal {got == exp}"
      if got != exp then
        let i := (List.range (min got.length exp.length)).find? fun i => got[i]! != exp[i]!
        IO.println s!"first diff at {i}"
        match i with
        | some i => IO.println s!"spec {got.drop (i-6) |>.take 14}\npar1 {exp.drop (i-6) |>.take 14}"
        | none => pure ()
