import Compiler.Front.PipeFront
open Proven
def f := compile% fun xs : Array UInt8 => xs.insertionSort
