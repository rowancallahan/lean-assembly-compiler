import Compiler.Front.Reify
open Proven
def minus (a b : BitVec 64) : BitVec 64 := if a < b then 0 else a - b
def e := reify% minus
