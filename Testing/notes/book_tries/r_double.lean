import Compiler.Front.Reify
open Proven
def double (x : BitVec 64) : BitVec 64 := x + x
def e := reify% double
