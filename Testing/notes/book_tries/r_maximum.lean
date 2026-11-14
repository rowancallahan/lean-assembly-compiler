import Compiler.Front.Reify
open Proven
def maximum (a b : BitVec 64) : BitVec 64 := if (if a < b then 1 else 0 : BitVec 64) = 0 then a else b
def e := reify% maximum
