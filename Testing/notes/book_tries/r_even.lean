import Compiler.Front.Reify
open Proven
def even (n : BitVec 64) : BitVec 64 := if n &&& 1 = 0 then 1 else 0
def e := reify% even
