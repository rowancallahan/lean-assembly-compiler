import Compiler.Front.PipeFront
open Proven
def sum := compile% fun xs : List UInt8 => xs.foldl (fun (a : BitVec 64) x => a + x.toBitVec.setWidth 64) 0
