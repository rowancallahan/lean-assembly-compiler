import Compiler.Front.Reify
open Proven
def isZero (n : BitVec 64) : Bool := n == 0
def e := reify% isZero
