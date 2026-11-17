import Nano.AsmSelf
import Nano.Link
import Nano.Gen
/- usage (repo root): NANO_DIR=DIR lake env lean --tstack=400000 Testing/nano/emit_link.lean   (DIR holds *.nano sources)
   Linker test data: the binary `Nano.Link.link nanoAsm.code nanoAsm.code` (two compiled stages linked by the 18-word
   stub; theorem `Nano.Link.link_stage`: it computes `asm ∘ asm`) -> Testing/asm/frontx-words/nanolink.{words,cases};
   per source: input = `genR p`, expected = executed Lean `asm (asm (genR p))`.  First line of the words file: a slot
   count S with `8 (S + 1) + 7 ≥ 4 K + 96`, K = the largest intermediate length / stage work space (the theorem's
   work-space bound). -/
open Nano
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
#eval show IO Unit from do
  let dir : System.FilePath := (← IO.getEnv "NANO_DIR").get!
  let files := (← dir.readDir).map (·.path) |>.filter (·.extension == some "nano") |>.toList
  let files := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  let mut cases := ""; let mut K := 8 * (Self.nanoAsm.slots + 1) + 7
  for f in files do
    let src ← IO.FS.readFile f
    match nanoElab src.toUTF8.toList with
    | none => throw (IO.userError s!"rejected {f}")
    | some p =>
      let recs := genR p
      let mid := Self.nanoAsm ⟨recs.toArray⟩
      K := max K mid.length
      cases := cases ++ s!"{hx recs} {hx (Self.nanoAsm ⟨mid.toArray⟩)}\n"
  let code := Nano.Link.link Self.nanoAsm.code Self.nanoAsm.code
  IO.FS.writeFile "Testing/asm/frontx-words/nanolink.cases" cases
  IO.FS.writeFile "Testing/asm/frontx-words/nanolink.words"
    (String.intercalate "\n" (toString ((4 * K + 96) / 8 + 1) :: code.map fun w =>
      let s := String.ofList (Nat.toDigits 16 (BitVec.toNat w)); "".pushn '0' (8 - s.length) ++ s) ++ "\n")
  IO.println s!"{files.length} programs, K = {K}, {code.length} words"
