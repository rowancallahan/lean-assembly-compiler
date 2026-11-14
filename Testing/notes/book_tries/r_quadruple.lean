import Compiler.Front.Reify
open Proven
def quadruple (x : BitVec 64) : BitVec 64 := x + x + x + x
def e := reify% quadruple
