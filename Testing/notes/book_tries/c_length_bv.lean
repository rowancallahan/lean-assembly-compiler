import Compiler.Front.PipeFront
open Proven
def f := compile% fun xs : List UInt8 => BitVec.ofNat 64 xs.length   -- Nat result restated as a 64-bit word
