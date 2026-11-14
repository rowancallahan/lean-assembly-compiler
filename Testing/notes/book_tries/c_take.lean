import Compiler.Front.PipeFront
open Proven
def f := compile% fun xs : List UInt8 => xs.take 5
