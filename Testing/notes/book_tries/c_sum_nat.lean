import Compiler.Front.PipeFront
open Proven
def sum := compile% fun xs : List Nat => xs.foldl (· + ·) 0   -- book: List Nat
