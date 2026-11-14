import Compiler.Front.Reify
open Proven
def pred (n : BitVec 64) : BitVec 64 := if n = 0 then 0 else n - 1
def e := reify% pred
