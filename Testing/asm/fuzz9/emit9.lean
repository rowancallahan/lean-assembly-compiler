/- `lake env lean Testing/asm/fuzz9/emit9.lean`: writes `Testing/asm/fuzz9/words/tinyrN.words` (first line `indw 1 m nl`, then the code) for the
TinyRepro entries r1, r2, r3, r5 (`implements1` work bounds: `Ind.spaceA 2 20`, `2 17`, `2 16` with the input's cells, `1 16 (M n)`). -/
import Riscv.Frontx.TinyRepro
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def emitW (name : String) (m nl : Nat) (code : List (BitVec 32)) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/fuzz9/words"
  IO.FS.writeFile s!"Testing/asm/fuzz9/words/{name}.words" (String.intercalate "\n" (s!"indw 1 {m} {nl}" :: code.map hex8) ++ "\n")
#eval do
  emitW "tinyr1" 2 20 TinyR1.comp.code
  emitW "tinyr2" 2 17 TinyR2.comp.code
  emitW "tinyr3" 2 16 TinyR3.comp.code
  emitW "tinyr5" 1 16 TinyR5.compile.code
