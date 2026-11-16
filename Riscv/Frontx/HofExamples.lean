/- Higher-order arguments by specialisation (NOTES §27): targets.

Book text verbatim from fp-lean @0abeea5 (`leanprover/fp-lean`, `examples/Examples/…`, line numbers given); core
definitions are Lean 4.29's own (`List.map`, `List.foldl`, …, nothing copied).  Each entry point `g : ByteArray → R`
is ours: it passes a known function to the higher-order definition, on the input bytes.  `frontx_hof_entry g`
specialises (`SpecHof.lean`), compiles the first-order copy with the existing translator and adds `g.prog`/`g.exec`;
`frontx_implements[_list] g` the machine theorem `g.implements1` (about `g` itself).  Nothing is proved by hand. -/
import Riscv.Frontx.SpecHof
import Riscv.Frontx.Impl1
import Compiler.Front.PipeStd

namespace Proven.Frontx.Hof
open Proven Proven.Frontx

/-! ## fp-lean, chapter 7, `MonadTransformers/Do.lean:93-128`: three versions of `find?` -/

namespace EarlyReturn

namespace Non
def List.find? (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    if p x then
      some x
    else
      find? p xs
end Non

def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    find? p xs

end EarlyReturn

/-- `EarlyReturn.Non.List.find? (· > 3)` on the input -/
def nonFindGt3 (xs : ByteArray) : Option UInt8 := EarlyReturn.Non.List.find? (· > 3) xs.data.toList
frontx_hof_entry nonFindGt3
frontx_implements nonFindGt3

/-- `EarlyReturn.List.find? (· > 3)` (`do`, `failure`, `return`) on the input -/
def findGt3 (xs : ByteArray) : Option UInt8 := EarlyReturn.List.find? (· > 3) xs.data.toList
frontx_hof_entry findGt3
frontx_implements findGt3

/-! ## fp-lean, chapter 9, `ProgramsProofs/TCO.lean:183-190`: `NonTail.filter` (used at `:204` with `(· > 3)`) -/

def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs

def filterGt3 (xs : ByteArray) : List UInt8 := NonTail.filter (· > 3) xs.data.toList
frontx_hof_entry filterGt3
frontx_implements_list filterGt3

/-! ## fp-lean, chapter 8, `DependentTypes/Finite.lean:118-120`: `List.foldr` (used at `:126` as `foldr (· + ·) 0`) -/

namespace ListExtras
def List.foldr (f : α → β → β) (default : β) : List α → β
  | []     => default
  | a :: l => f a (foldr f default l)
end ListExtras

def foldrSum (xs : ByteArray) : Nat := ListExtras.List.foldr (· + ·) 0 (xs.data.toList.map UInt8.toNat)
frontx_hof_entry foldrSum
frontx_implements foldrSum

/-! ## fp-lean, chapter 8, `DependentTypes/DB.lean:458-460`: `List.flatMap` -/

namespace Mine
def List.flatMap (f : α → List β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x ++ xs.flatMap f
end Mine

def dupAll (xs : ByteArray) : List UInt8 := Mine.List.flatMap (fun x => [x, x]) xs.data.toList
frontx_hof_entry dupAll
frontx_implements_list dupAll

/-! ## fp-lean, chapter 9, `ProgramsProofs/Arrays.lean:293-306`: `findHelper`, `Array.find` -/

def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none

def Array.find (arr : Array α) (p : α → Bool) :
    Option (Nat × α) :=
  findHelper arr p 0

def arrFindGt3 (xs : ByteArray) : Option (Nat × UInt8) := Array.find xs.data (· > 3)
frontx_hof_entry arrFindGt3
frontx_implements_bytes arrFindGt3

/-! ## Lean core higher-order functions (`List.map`, `foldl`, `filter`, `any`, `all`, `find?`, `countP`,
`Function.comp`, `Array.foldl`), each with a lambda, a named function or a partial application -/

def mapInc (xs : ByteArray) : List UInt8 := xs.data.toList.map (· + 1)
frontx_hof_entry mapInc
frontx_implements_list mapInc

def mapComp (xs : ByteArray) : List UInt8 := xs.data.toList.map ((· ^^^ 0x5A) ∘ (· + 7))
frontx_hof_entry mapComp
frontx_implements_list mapComp

def sumFoldl (xs : ByteArray) : Nat := xs.data.toList.foldl (fun acc x => acc + x.toNat) 0
frontx_hof_entry sumFoldl
frontx_implements sumFoldl

def xorArr (xs : ByteArray) : UInt8 := xs.data.foldl (· ^^^ ·) 0
frontx_hof_entry xorArr
frontx_implements xorArr

def filterNZ (xs : ByteArray) : List UInt8 := xs.data.toList.filter (· != 0)
frontx_hof_entry filterNZ
frontx_implements_list filterNZ

def anyNL (xs : ByteArray) : Bool := xs.data.toList.any (· == 10)
frontx_hof_entry anyNL
frontx_implements anyNL

def allAscii (xs : ByteArray) : Bool := xs.data.toList.all (· < 128)
frontx_hof_entry allAscii
frontx_implements allAscii

def findHigh (xs : ByteArray) : Option UInt8 := xs.data.toList.find? (· ≥ 128)
frontx_hof_entry findHigh
frontx_implements findHigh

def countSp (xs : ByteArray) : Nat := xs.data.toList.countP (· == 32)
frontx_hof_entry countSp
frontx_implements countSp

/-! ## The compiler's own pipeline semantics (`Compiler/Front/Pipe.lean:125`, `PipeStd.lean:171`) at a known stage:
`Stage.denote (.map e)` is `l.map fun x => e.denote 0 x`; the closure and `ByteExp.denote` on the known `e` are
specialised and evaluated -/

def stageMap (xs : ByteArray) : List UInt8 :=
  Stage.denote (.map (.bin .xor (.bin .add .x (.lit 3)) (.lit 0x20))) xs.data.toList
frontx_hof_entry stageMap
frontx_implements_list stageMap

/-- a pipe of two stages (`Pipe.denote`, `Pipe.lean:137`, a `foldl` over the stages): unrolled, the two `map`s
fused (`List.map_map`) -/
def pipe2 (xs : ByteArray) : List UInt8 :=
  Pipe.denote [.map (.bin .add .x (.lit 1)), .map (.bin .and .x (.lit 0x7F))] xs.data.toList
frontx_hof_entry pipe2
frontx_implements_list pipe2

def xstageFilter (xs : ByteArray) : List UInt8 :=
  XStage.denote (.filter (.and (.cmp .le (.lit 48) .x) (.cmp .le .x (.lit 57)))) xs.data.toList
frontx_hof_entry xstageFilter
frontx_implements_list xstageFilter

end Proven.Frontx.Hof
