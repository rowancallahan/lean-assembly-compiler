import Proven.Frontx.ForMachine
open Proven Proven.Frontx.Ex
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def emit (name : String) (code : List (BitVec 32)) : IO Unit :=
  IO.FS.writeFile s!"asm/arr-words/{name}.words" (String.intercalate "\n" (code.map hex8) ++ "\n")
#eval emit "crc" crcCode
#eval emit "b64sum" b64Code
#eval emit "find" findCode
#eval emit "be32" be32Code
#eval IO.println s!"slots: crc {crcGo.slots} b64sum {b64Sum.slots} find {findByte.slots} be32 {be32.slots}"
