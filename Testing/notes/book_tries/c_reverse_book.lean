import Compiler.Front.PipeFront
open Proven
def reverse (xs : List α) : List α := xs.foldl (fun r x => x :: r) []
def f := compile% fun xs : List UInt8 => reverse xs   -- book-style def as is
