import Nano.AsmSelf
import Nano.Gen
/- usage (repo root): NANO_DIR=DIR lake env lean Testing/nano/emit_nano.lean   (DIR holds the *.nano sources)
   writes Testing/asm/frontx-words/nanoasm.{words,cases}: the machine-theorem binary of the assembler stage and,
   per source, the record bytes (nanoElab + genR) with the result of executed Lean `asm`; and DIR/index.txt:
   `source-file records-hex code-hex` (code = nanoGen = executed Lean). -/
open Nano
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : UInt64 := UInt64.ofNat ((i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j + 12345) % 2^64)
def argsFor (k i : Nat) : List UInt64 := (List.range k).map fun j =>
  match (i + j) % 5 with | 0 => 0 | 1 => 1 | 2 => 0 - 1 | _ => rnd i j
#eval show IO Unit from do
  let dir : System.FilePath := (← IO.getEnv "NANO_DIR").get!
  let files := (← dir.readDir).map (·.path) |>.filter (·.extension == some "nano") |>.toList
  let files := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  let mut cases := ""; let mut idx := ""
  for f in files do
    let src ← IO.FS.readFile f
    match nanoElab src.toUTF8.toList with
    | none => throw (IO.userError s!"rejected {f}")
    | some p =>
      let recs := genR p
      cases := cases ++ s!"{hx recs} {hx (Self.nanoAsm ⟨recs.toArray⟩)}\n"
      let runs := (List.range 6).map fun i =>
        let a := argsFor p.1 i
        s!"{String.intercalate "," (a.map toString)}={(p.eval a).getD 0}"
      idx := idx ++ s!"{f} {hx recs} {hx (nanoGen p)} {String.intercalate ";" runs}\n"
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile "Testing/asm/frontx-words/nanoasm.cases" cases
  IO.FS.writeFile (dir / "index.txt") idx
  IO.FS.writeFile "Testing/asm/frontx-words/nanoasm.words"
    (String.intercalate "\n" (toString Self.nanoAsm.slots :: Self.nanoAsm.code.map fun w =>
      let s := String.ofList (Nat.toDigits 16 (BitVec.toNat w)); "".pushn '0' (8 - s.length) ++ s) ++ "\n")
  IO.println s!"{files.length} programs"
