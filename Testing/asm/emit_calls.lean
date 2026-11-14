import Riscv.Examples.CallExamples
open Proven Proven.Mach Proven.Mach.Riscv
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def emit (n : String) (c : List (BitVec 32)) : IO Unit :=
  IO.FS.writeFile s!"Testing/asm/calls-words/{n}.words" (String.intercalate "\n" (c.map hex8) ++ "\n")
#eval emit "sumto" (callsCode sumToProg 0)
#eval emit "fib" (callsCode fibProg 0)
#eval emit "even" (callsCode evenProg 0)
