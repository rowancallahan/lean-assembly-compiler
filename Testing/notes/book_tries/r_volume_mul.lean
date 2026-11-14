import Compiler.Front.Reify
open Proven
def volume (a b c : BitVec 64) : BitVec 64 := a * b * c
def e := reify% volume
