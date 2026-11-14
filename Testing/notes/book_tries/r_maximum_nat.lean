import Compiler.Front.Reify
open Proven
def maximum (a b : BitVec 64) : BitVec 64 := if a < b then b else a   -- natural restatement
def e := reify% maximum
