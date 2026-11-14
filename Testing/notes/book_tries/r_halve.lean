import Compiler.Front.Reify
open Proven
def halve (n : BitVec 64) : BitVec 64 := n >>> ((1 : BitVec 64).toNat % 64)
def e := reify% halve
