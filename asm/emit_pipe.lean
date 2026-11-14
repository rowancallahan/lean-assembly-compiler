import Proven.PipeExamples
open Proven Proven.PipeEx
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
/-- words, and the table `Pipe.space p n` for `n = 0..64` -/
def emit {α : Type} {enc : α → List UInt8} {f : List UInt8 → α} (n : String) (c : Compiled enc f) : IO Unit := do
  IO.FS.createDirAll "asm/pipe-words"
  IO.FS.writeFile s!"asm/pipe-words/{n}.words" (String.intercalate "\n" (c.code.map hex8) ++ "\n")
  IO.FS.writeFile s!"asm/pipe-words/{n}.space"
    (String.intercalate " " ((List.range 65).map fun k => toString (Pipe.space c.pipe k)) ++ "\n")
#eval do
  emit "revinc5" revinc5; emit "mapsum" mapsum; emit "revtake5" revtake5; emit "mapsort" mapsort
  emit "sort" sort; emit "sum64" sum64; emit "hash64" hash64; emit "sortdesc" sortdesc; emit "mid" mid
  emit "foldsorted" foldsorted; emit "twosort" twosort
