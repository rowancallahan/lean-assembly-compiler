import Nano.Base.Riscv.Back.OptB
import Nano.Base.Riscv.Direct.SortMergeMachine
open Proven
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
#eval show IO Unit from do
  match compileOptB 7 [0, 2, 3] msortProg with
  | .ok ws =>
    IO.FS.writeFile "Testing/asm/opt-words/msort.words" (String.intercalate "\n" (ws.map hex8) ++ "\n")
    IO.println s!"msort: {ws.length} words (old {msortCode.length})"
  | .error e => throw (IO.userError e)
  let cs := Mach.Riscv.candidates (Mach.Riscv.toMS msortProg) 7
  IO.println s!"{cs.length} candidates; first passing: {cs.find? fun c => (Mach.Riscv.tryB 7 [0, 2, 3] (Mach.Riscv.toMS msortProg) c).isSome}"
