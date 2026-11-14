import Compiler.Front.Reify
open Proven
def add1 (n : Nat) : Nat := n + 1   -- as in the book
def e := reify% add1
