import Nano.SelfHostedA
import Nano.Ser
/- usage (repo root): NANO_DIR=DIR lake env lean --tstack=400000 Testing/nano/emit_linkA.lean
   Linked-binary test data (nano-closeA) for Testing/asm/frontx_test.py:
   * `nanolexlink` = `link vBE.code eBE.code` (theorem: `link_stage` + `eB_vB`: computes `lexB`), per file: input =
     the file's bytes, expected = executed Lean `lexB` (the stage-1 SPEC);
   * `nanotail` = `link nanoExpM.code nanoAsm.code` (computes `asm ∘ mexp`), per accepted source: input = `ser p`,
     expected = executed Lean `nanoGen p` (the compiled program's code).
   First line of a words file: a slot count S with `8 (S + 1) + 7 ≥ 4 K + 96` (the linked work space), K = the largest
   intermediate length / stage work space. -/
open Nano Nano.SelfHost
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def words (K : Nat) (code : List (BitVec 32)) : String :=
  String.intercalate "\n" (toString ((4 * K + 96) / 8 + 1) :: code.map fun w =>
    let s := String.ofList (Nat.toDigits 16 (BitVec.toNat w)); "".pushn '0' (8 - s.length) ++ s) ++ "\n"
#eval show IO Unit from do
  let dir : System.FilePath := (← IO.getEnv "NANO_DIR").get!
  let files := (← dir.readDir).map (·.path) |>.toList
  let files := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  let mut cl := ""; let mut ct := ""; let mut n := 0; let mut m := 0
  let mut K1 := max (8 * (Self.vBE.slots + 1) + 7) (8 * (Self.eBE.slots + 1) + 7)
  let mut K2 := max (8 * (Self.nanoExpM.slots + 1) + 7) (8 * (Self.nanoAsm.slots + 1) + 7)
  for f in files do
    let bs := (← IO.FS.readBinFile f).toList
    K1 := max K1 (B.vB bs).length
    cl := cl ++ s!"{hx bs} {hx (B.lexB bs)}\n"; n := n + 1
    if let some p := nanoElab bs then
      let s := ser p
      K2 := max K2 (mexp s).length
      ct := ct ++ s!"{hx s} {hx (nanoGen p)}\n"; m := m + 1
  IO.FS.writeFile "Testing/asm/frontx-words/nanolexlink.cases" cl
  IO.FS.writeFile "Testing/asm/frontx-words/nanotail.cases" ct
  IO.FS.writeFile "Testing/asm/frontx-words/nanolexlink.words" (words K1 (Link.link Self.vBE.code Self.eBE.code))
  IO.FS.writeFile "Testing/asm/frontx-words/nanotail.words" (words K2 (Link.link Self.nanoExpM.code Self.nanoAsm.code))
  IO.println s!"nanolexlink: {n} cases (K = {K1}); nanotail: {m} cases (K = {K2})"
