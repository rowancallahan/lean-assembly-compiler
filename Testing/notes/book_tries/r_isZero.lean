import Compiler.Front.Reify
open Proven
def isZero (n : BitVec 64) : BitVec 64 := if n = 0 then 1 else 0
def e := reify% isZero
