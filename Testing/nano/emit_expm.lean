import Legacy.Nano.ExpandMSelf
import Legacy.Nano.Ser
/- usage (repo root): NANO_DIR=DIR NANO_STAGE=expm|lex lake env lean --tstack=400000 Testing/nano/emit_expm.lean
   Stage test data (nano-closeA) for Testing/asm/frontx_test.py: the compiled stage's words and per case input /
   expected result, the result computed by executed Lean on the SPEC function (`Nano.mexp` resp. `Nano.B.lexB`), not
   on the compiled machine's Lean form.  DIR holds `*.nano` sources and `*.bin` raw inputs.
   expm: input = `ser p` for every accepted source, plus the raw inputs; lex: input = the source bytes and the raw
   inputs. -/
open Nano
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
#eval show IO Unit from do
  let dir : System.FilePath := (← IO.getEnv "NANO_DIR").get!
  let stage := (← IO.getEnv "NANO_STAGE").get!
  let files := (← dir.readDir).map (·.path) |>.toList
  let files := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  let mut cases := ""; let mut n := 0
  for f in files do
    let bs := (← IO.FS.readBinFile f).toList
    let inp? : Option (List UInt8) :=
      if f.extension == some "nano" then
        (if stage == "expm" then (nanoElab bs).map ser else some bs)
      else some bs
    if let some inp := inp? then
      let out := if stage == "expm" then mexp inp else mexp inp
      cases := cases ++ s!"{hx inp} {hx out}\n"; n := n + 1
  let (nm, code, slots) := if stage == "expm" then ("nanoexpm", Self.nanoExpM.code, Self.nanoExpM.slots)
    else ("nanoexpm", Self.nanoExpM.code, Self.nanoExpM.slots)
  IO.FS.writeFile s!"Testing/asm/frontx-words/{nm}.cases" cases
  IO.FS.writeFile s!"Testing/asm/frontx-words/{nm}.words"
    (String.intercalate "\n" (toString slots :: code.map fun w =>
      let s := String.ofList (Nat.toDigits 16 (BitVec.toNat w)); "".pushn '0' (8 - s.length) ++ s) ++ "\n")
  IO.println s!"{nm}: {n} cases, {code.length} words, {slots} slots"
