import Compiler.Front.Reify
open Proven
def minus (a b : BitVec 64) : BitVec 64 := if (if a < b then 1 else 0 : BitVec 64) = 0 then a - b else 0
def e := reify% minus
