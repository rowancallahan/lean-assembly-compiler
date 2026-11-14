import Proven.SortMachine
open Proven
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def emit (n : String) (ws : List (BitVec 32)) : IO Unit :=
  IO.FS.writeFile s!"asm/arr-words/{n}.words" (String.intercalate "\n" (ws.map hex8) ++ "\n")
#eval do emit "sum" sumCode; emit "take" takeCode; emit "inc" incCode; emit "sort" sortCode
