import Compiler.Front.Reify
open Proven
def triple (x : BitVec 64) : BitVec 64 := x + x + x
def e := reify% triple
