import Riscv.Examples.Crc
open Proven
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
#eval IO.FS.writeFile "Testing/asm/arr-words/crc.words" (String.intercalate "\n" (Crc.crcCode.map hex8) ++ "\n")
