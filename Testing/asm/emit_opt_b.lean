import Riscv.Back.OptB
import Riscv.Direct.SortMergeMachine
open Proven
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
#eval show IO Unit from do
  match compileOptB 7 [0, 2, 3] msortProg with
  | .ok ws =>
    IO.FS.writeFile "Testing/asm/opt-words/msort.words" (String.intercalate "\n" (ws.map hex8) ++ "\n")
    IO.println s!"msort: {ws.length} words (old {msortCode.length})"
  | .error e => throw (IO.userError e)
  for T in [1, 2, 3, 4, 5, 6] do
    IO.println s!"T={T}: {(Mach.Riscv.tryB 7 [0, 2, 3] (Mach.Riscv.toMS msortProg) T).map (·.length)} regs {Mach.Riscv.pickRegs (Mach.Riscv.toMS msortProg) 7 (6 - T)}"
