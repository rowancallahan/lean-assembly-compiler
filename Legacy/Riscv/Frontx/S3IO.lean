/- Byte formats for the S3 examples (`Riscv/Frontx/S3Examples*.lean`): plain Lean functions on byte lists, compiled
through S3 together with the function under test (`main = encodeOut ∘ f ∘ decodeIn`).  They are harness, not
trusted: each example's theorem is about its `main` on the raw bytes, `Computes P main id id`, and `main` is the
displayed composition. -/
import Legacy.Compiler.S3.Front
import Legacy.Riscv.Frontx.IndExamples

namespace Proven.S3.Ex
open Proven.Frontx.IndEx

/-- a word as 8 bytes, little-endian -/
def enc8 (x : UInt64) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8,
   (x >>> 32).toUInt8, (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8]

/-- 4 bytes as a word, little-endian (the IR back end takes at most 7 call arguments) -/
def w4 (b0 b1 b2 b3 : UInt8) : UInt64 :=
  b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24)

/-- words, 8 bytes each, little-endian (a short tail is dropped) -/
def decW : List UInt8 → List UInt64
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest => (w4 b0 b1 b2 b3 ||| (w4 b4 b5 b6 b7 <<< 32)) :: decW rest
  | _ => []

def encW : List UInt64 → List UInt8
  | [] => []
  | x :: xs => enc8 x ++ encW xs

/-- trees in postorder: `0` a leaf, `1 x` a branch with payload byte `x` of the two trees before it (a stack
machine) -/
def decTGo : List UInt8 → List (BinTree UInt64) → List (BinTree UInt64)
  | [], st => st
  | b :: rest, st =>
    if b == 0 then decTGo rest (.leaf :: st)
    else match rest with
      | [] => st
      | x :: rest' => match st with
        | [] => st
        | [_] => st
        | r :: l :: st' => decTGo rest' (.branch l x.toUInt64 r :: st')

def encT : BinTree UInt64 → List UInt8
  | .leaf => [0]
  | .branch l x r => encT l ++ encT r ++ [1, x.toUInt8]

def decT (bs : List UInt8) : BinTree UInt64 :=
  match decTGo bs [] with
  | t :: _ => t
  | [] => .leaf

/-- a `Pos` as `n` ones then a zero (`n + 1`) -/
def decP : List UInt8 → Pos × List UInt8
  | [] => (.one, [])
  | b :: r => if b == 0 then (.one, r) else
    match decP r with
    | (p, r') => (.succ p, r')

def encP : Pos → List UInt8
  | .one => [0]
  | .succ p => 1 :: encP p

def boolB (b : Bool) : List UInt8 := [if b then 1 else 0]

s3_enc BinTree
s3_enc Pos

end Proven.S3.Ex
