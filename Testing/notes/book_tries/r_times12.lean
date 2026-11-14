import Compiler.Front.Reify
open Proven
def timesTwelve (x : BitVec 64) : BitVec 64 := (x <<< ((3 : BitVec 64).toNat % 64)) + (x <<< ((2 : BitVec 64).toNat % 64))
def e := reify% timesTwelve
