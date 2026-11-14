import Proven.CompilerArm
import Proven.CodeFast
import Proven.CompilerArmFast
open Proven
def v (i : Fin 4) : Exp := .var i
def demoE : Exp := .bin .sub (.bin .xor (.bin .add (v 0) (v 1)) (.bin .and (v 2) (.const 0xff))) (.bin .or (v 3) (.const 0x1234))
def demo2E : Exp := .ite (.bin .xor (.bin .ult (v 0) (v 1)) (.bin .slt (v 0) (v 2)))
  (.bin .sub (.bin .eq (v 2) (v 3)) (.bin .ashr (v 2) (v 0)))
  (.bin .add (.bin .shl (v 0) (v 3)) (.bin .lshr (v 1) (v 2)))
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def emit (n : String) (ws : List (BitVec 32)) : IO Unit :=
  IO.FS.writeFile s!"bench/exp-words/{n}.words" (String.intercalate "\n" (ws.map hex8) ++ "\n")
#eval show IO Unit from do
  for (n, e) in [("demo", demoE), ("demo2", demo2E)] do
    emit (n ++ "-rv-std") (compile e); emit (n ++ "-rv-fast") (Fast.compile e)
    emit (n ++ "-arm-std") (Arm.compile e); emit (n ++ "-arm-fast") (Arm.Fast.compile e)
