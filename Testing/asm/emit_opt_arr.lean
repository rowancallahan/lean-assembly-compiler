import Riscv.Back.OptArr
import Riscv.Direct.SortMachine
open Proven
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def put (name : String) (r : Except String (List (BitVec 32))) : IO Unit :=
  match r with
  | .ok ws => do
    IO.FS.writeFile s!"Testing/asm/opt-words/{name}.words" (String.intercalate "\n" (ws.map hex8) ++ "\n")
    IO.println s!"{name}: {ws.length} words"
  | .error e => throw (IO.userError s!"{name}: {e}")
#eval do
  put "sum" (compileOptA [0] sumProg)
  put "take" (compileOptA [0, 3] (mapProg (.var 6)))
  put "inc" (compileOptA [0, 3] (mapProg (.bin .add (.var 6) (.const 1))))
  put "insertion" (compileOptA [0, 3] sortProg)
