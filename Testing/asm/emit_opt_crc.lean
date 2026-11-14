/- CRC-32 words, old (`rvF.compBF`) and optimised (`compBFO`); program copied from `Riscv/Examples/Crc.lean`
on main (definitions only). -/
import Riscv.Back.OptB
open Proven Proven.Mach Proven.Mach.Riscv
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def poly : BitVec 64 := 0xEDB88320
def stepE : Mach.BExp :=
  .bin .xor (.bin .lshr (.var 5) (.const 1)) (.ite (.bin .and (.var 5) (.const 1)) (.const poly) (.const 0))
def rep : Nat → Mach.BStmt → Mach.BStmt
  | 0, p => p
  | n + 1, p => .seq p (rep n p)
def tableLoop : Mach.BStmt :=
  .loop (.bin .ult (.var 4) (.const 256))
    (.seq (.assign 5 (.var 4)) (.seq (rep 7 (.assign 5 stepE))
      (.seq (.store64 0 (.var 4) (.var 5)) (.assign 4 (.bin .add (.var 4) (.const 1))))))
def mainLoop : Mach.BStmt :=
  .loop (.bin .ult (.var 4) (.var 1))
    (.seq (.load 6 0 (.var 4)) (.seq (.load64 7 0 (.bin .and (.bin .xor (.var 5) (.var 6)) (.const 255)))
      (.seq (.assign 5 (.bin .xor (.var 7) (.bin .lshr (.var 5) (.const 8))))
        (.assign 4 (.bin .add (.var 4) (.const 1))))))
def store8 : Nat → Mach.BStmt
  | 0 => .store 1 (.const 0) (.var 4)
  | j + 1 => .seq (store8 j) (.store 1 (.const (BitVec.ofNat 64 (j + 1)))
      (.bin .lshr (.var 4) (.const (BitVec.ofNat 64 (8 * (j + 1))))))
def crcP : Mach.BStmt :=
  .seq (.assign 4 (.const 0)) (.seq tableLoop (.seq (.assign 5 (.const 0xFFFFFFFF)) (.seq (.assign 4 (.const 0))
    (.seq mainLoop (.seq (.assign 4 (.bin .xor (.var 5) (.const 0xFFFFFFFF))) (store8 3))))))
def wr (f : String) (ws : List (BitVec 32)) : IO Unit :=
  IO.FS.writeFile f (String.intercalate "\n" (ws.map hex8) ++ "\n")
#eval show IO Unit from do
  let old := rvF.codeF (rvF.compBF 0 [0, 3] [2] crcP)
  let new := compBFO 0 [0, 3] [2] crcP
  wr "Testing/asm/arr-words/crc.words" old
  wr "Testing/asm/opt-words/crc.words" new
  let opt := (firstB (fun c => tryB 0 [0, 3] crcP c [2]) (candidates crcP 0)).isSome
  IO.println s!"crc: old {old.length} words, new {new.length} words, optimised path: {opt}"
