import Nano.ElabBVSelf
import Nano.ElabBESelf
/- usage (repo root): NANO_DIR=DIR lake env lean --tstack=400000 Testing/nano/emit_lexsplit.lean
   Stage test data (nano-closeA) for the two halves of the split lexer: `nanolexv` (compiled `vB`, expected = executed
   Lean `vB src`) and `nanolexe` (compiled `eB` on input `vB src`, expected = executed Lean `lexB src`, the SPEC of
   stage 1: so the test also checks `eB_vB` on the data).  DIR holds the sources (any file). -/
open Nano
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def words (slots : Nat) (code : List (BitVec 32)) : String :=
  String.intercalate "\n" (toString slots :: code.map fun w =>
    let s := String.ofList (Nat.toDigits 16 (BitVec.toNat w)); "".pushn '0' (8 - s.length) ++ s) ++ "\n"
#eval show IO Unit from do
  let dir : System.FilePath := (← IO.getEnv "NANO_DIR").get!
  let files := (← dir.readDir).map (·.path) |>.toList
  let files := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  let mut cv := ""; let mut ce := ""; let mut n := 0
  for f in files do
    let bs := (← IO.FS.readBinFile f).toList
    let v := B.vB bs
    cv := cv ++ s!"{hx bs} {hx v}\n"
    ce := ce ++ s!"{hx v} {hx (B.lexB bs)}\n"; n := n + 1
  IO.FS.writeFile "Testing/asm/frontx-words/nanolexv.cases" cv
  IO.FS.writeFile "Testing/asm/frontx-words/nanolexe.cases" ce
  IO.FS.writeFile "Testing/asm/frontx-words/nanolexv.words" (words Self.vBE.slots Self.vBE.code)
  IO.FS.writeFile "Testing/asm/frontx-words/nanolexe.words" (words Self.eBE.slots Self.eBE.code)
  IO.println s!"nanolexv / nanolexe: {n} cases, {Self.vBE.code.length} + {Self.eBE.code.length} words"
