import Riscv.Examples.PipeExamples
open Proven Proven.PipeEx
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
/-- words, and the table `Pipe.space p n` for `n = 0..64` -/
def emit {α : Type} {enc : α → List UInt8} {f : List UInt8 → α} (n : String) (c : Compiled enc f) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/pipe-words"
  IO.FS.writeFile s!"Testing/asm/pipe-words/{n}.words" (String.intercalate "\n" (c.code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/pipe-words/{n}.space"
    (String.intercalate " " ((List.range 65).map fun k => toString (XPipe.space c.pipe k)) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/pipe-words/{n}.sspace"
    (String.intercalate " " ((List.range 65).map fun k => toString (XPipe.sspace c.pipe k)) ++ "\n")
#eval do
  emit "revinc5" revinc5; emit "mapsum" mapsum; emit "revtake5" revtake5; emit "mapsort" mapsort
  emit "sort" sort; emit "sum64" sum64; emit "hash64" hash64; emit "sortdesc" sortdesc; emit "mid" mid
  emit "foldsorted" foldsorted; emit "twosort" twosort
  emit "len" len; emit "sum8" sum8; emit "sumNat" sumNat; emit "countLt" countLt; emit "count7" count7
  emit "any3" any3; emit "allRange" allRange; emit "has5" has5; emit "empty" empty
  emit "head" head; emit "last" last; emit "get3" get3; emit "findBig" findBig; emit "min" min; emit "max" max
  emit "idxZero" idxZero; emit "idx42" idx42
  emit "evens" evens; emit "ascii" ascii; emit "unpad" unpad; emit "suffix" suffix; emit "prefixRev" prefixRev
  emit "filtmap" filtmap; emit "filtsort" filtsort; emit "countBig" countBig
