-- words of the `Implements1` examples, unoptimised (`Testing/asm/impl1-words/`) and optimised
-- (`Testing/asm/impl1-opt-words/`); tested by `Testing/asm/impl1_test.py`
import Riscv.Examples.Implements1Opt
open Proven Proven.Mach.Riscv
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def put (d n : String) (ws : List (BitVec 32)) : IO Unit := do
  IO.FS.createDirAll s!"Testing/asm/{d}"
  IO.FS.writeFile s!"Testing/asm/{d}/{n}.words" (String.intercalate "\n" (ws.map hex8) ++ "\n")
  IO.println s!"{d}/{n}: {ws.length} words"
#eval do
  put "impl1-words" "take5" (takeCode1 5); put "impl1-opt-words" "take5" (takeCodeO 5)
  put "impl1-words" "inc" incCode1; put "impl1-opt-words" "inc" incCodeO
  put "impl1-words" "sum" sumCode1; put "impl1-opt-words" "sum" sumCodeO
  put "impl1-words" "crc" Crc.crcCode; put "impl1-opt-words" "crc" Crc.crcCodeO
  put "impl1-words" "sort" sortCode; put "impl1-opt-words" "sort" sortCodeO
  put "impl1-words" "msort" msortCode; put "impl1-opt-words" "msort" msortCodeO
