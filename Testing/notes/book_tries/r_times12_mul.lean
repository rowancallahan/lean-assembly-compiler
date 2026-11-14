import Compiler.Front.Reify
open Proven
def timesTwelve (x : BitVec 64) : BitVec 64 := x * 12   -- natural restatement
def e := reify% timesTwelve
