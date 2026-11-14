import Riscv.Frontx.Machine
open Proven Proven.Frontx.Ex
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
/-- first line: the number of slots (work space = `8 * (slots + 1) + 7`); then the code words -/
def emit (name : String) (slots : Nat) (code : List (BitVec 32)) : IO Unit := do
  IO.FS.createDirectoryAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words" (String.intercalate "\n" (toString slots :: code.map hex8) ++ "\n")
#eval emit "crcraw" crcRaw.slots crcRaw.code
#eval emit "b64all" b64All.slots b64All.code
#eval emit "findnl" findNL.slots findNL.code
#eval emit "be32at0" be32At0.slots be32At0.code
