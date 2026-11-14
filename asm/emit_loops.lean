import Proven.LoopExamples
open Proven
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
#eval do
  IO.FS.writeFile "asm/loop-words/sum.words" (String.intercalate "\n" ((compileF sumProg).map hex8) ++ "\n")
  IO.FS.writeFile "asm/loop-words/gcd.words" (String.intercalate "\n" ((compileF gcdProg).map hex8) ++ "\n")
