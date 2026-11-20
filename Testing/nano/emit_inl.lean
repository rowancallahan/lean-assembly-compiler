import Nano.InlPSelf
import Legacy.Nano.ElabU
/- usage (repo root): NANO_DIR=DIR lake env lean --tstack=400000 Testing/nano/emit_inl.lean   (DIR holds *.nano sources)
   Inliner stage test data (branch nano-closeB): the compiled paged inliner `Nano.IP.inlP.pg.body` (theorem
   `Nano.IP.inlP_implements`, work space 8192 * 601) -> Testing/asm/frontx-words/nanoinl.{words,cases}; per source:
   input = `serU u` (`u = nanoElabU src`), expected = executed Lean `inlB (serU u)` (checked == `inlP` in Lean). -/
open Nano
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def hex8 (w : BitVec 32) : String :=
  let s := String.ofList (Nat.toDigits 16 w.toNat); String.ofList (List.replicate (8 - s.length) '0') ++ s
#eval show IO Unit from do
  let dir : System.FilePath := (← IO.getEnv "NANO_DIR").get!
  let files := (← dir.readDir).map (·.path) |>.filter (·.extension == some "nano") |>.toList
  let files := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  let mut cases := ""
  for f in files do
    let src ← IO.FS.readFile f
    match U.nanoElabU src.toUTF8.toList with
    | none => pure ()
    | some u =>
      let x := U.serU u
      let e := U.inlB x
      let m := (IP.inlP ⟨x.toArray⟩).toList
      if m != e then throw (IO.userError s!"Lean mismatch {f}")
      cases := cases ++ s!"{hx x} {hx e} {8192 * 601} 0\n"
  IO.FS.writeFile "Testing/asm/frontx-words/nanoinl.cases" cases
  IO.FS.writeFile "Testing/asm/frontx-words/nanoinl.words"
    (String.intercalate "\n" ("pg 1" :: IP.inlP.pg.body.map hex8) ++ "\n")
