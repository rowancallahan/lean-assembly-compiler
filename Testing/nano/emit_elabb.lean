import Nano.ElabBSelf
import Nano.ElabBProof
/- usage (repo root): lake env lean Testing/nano/emit_elabb.lean   after Testing/nano/elabb_inputs.py N SEED >
   Testing/nano/work/elabb_in.txt.  Writes Testing/asm/frontx-words/lexbe.{words,cases}: the machine-theorem binary of
   stage 1 (`Nano.Self.lexBE`) and per input the bytes computed by executed Lean `lexBE`; checks on the Lean side that
   these bytes decode to the spec (`decL (lexB x) = lexT x`, the lexer of `nanoElab`) and counts inputs `nanoElab`
   accepts / rejects. -/
open Nano Nano.B
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def parseLine (s : String) : List UInt8 :=
  ((s.splitOn " ").drop 1).filter (· ≠ "") |>.map (fun x => x.toNat!.toUInt8)
#eval show IO Unit from do
  let ls ← IO.FS.lines "Testing/nano/work/elabb_in.txt"
  let mut cases := ""; let mut acc := 0; let mut lexed := 0; let mut bad := 0
  for l in ls do
    let x := parseLine l
    let out := Self.lexBE ⟨x.toArray⟩
    if lexBytes (decL out) != lexBytes (lexT x) then bad := bad + 1
    if (lexT x).isSome then lexed := lexed + 1
    if (nanoElab x).isSome then acc := acc + 1
    cases := cases ++ s!"{hx x} {hx out}\n"
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile "Testing/asm/frontx-words/lexbe.cases" cases
  IO.FS.writeFile "Testing/asm/frontx-words/lexbe.words"
    (String.intercalate "\n" (toString Self.lexBE.slots :: Self.lexBE.code.map fun w =>
      let s := String.ofList (Nat.toDigits 16 (BitVec.toNat w)); "".pushn '0' (8 - s.length) ++ s) ++ "\n")
  IO.println s!"{ls.size} inputs: {lexed} pass stage 1 (lexT some), {acc} accepted by nanoElab, {ls.size - acc} rejected; {bad} spec mismatches; {Self.lexBE.code.length} words, {Self.lexBE.slots} slots"
