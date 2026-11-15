-- words of the boot stub (`Riscv/Back/Boot.lean`) and of the two examples of `Riscv/Examples/BootEx.lean`,
-- into `Testing/asm/boot-words/`; tested by `Testing/asm/boot_test.py`
import Riscv.Examples.BootEx
open Proven
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def put (n : String) (ws : List (BitVec 32)) : IO Unit := do
  IO.FS.writeFile s!"Testing/asm/boot-words/{n}.words" (String.intercalate "\n" (ws.map hex8) ++ "\n")
  IO.println s!"boot-words/{n}: {ws.length} words"
#eval do
  put "stub" Boot.stub
  put "revinc5" PipeEx.revinc5.code1
  put "inc" Mach.Riscv.incCode1
