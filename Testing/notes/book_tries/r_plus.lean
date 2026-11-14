import Compiler.Front.Reify
open Proven
def plus (a b : BitVec 64) : BitVec 64 := a + b
def e := reify% plus
