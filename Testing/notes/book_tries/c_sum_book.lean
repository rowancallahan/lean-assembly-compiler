import Compiler.Front.PipeFront
open Proven
namespace Tail
def sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs
def sum (xs : List Nat) : Nat := sumHelper 0 xs
end Tail
def s := compile% fun xs : List UInt8 => Tail.sum (xs.map UInt8.toNat)   -- book def as is
