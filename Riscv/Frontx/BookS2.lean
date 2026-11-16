/- Book survey 3, second third of the example files, retried with the higher-order front end (NOTES §27).

Book text verbatim from fp-lean @0abeea5 (`examples/Examples/…`, line numbers given; the `ANCHOR` comments removed).
Each entry `g : ByteArray → R` is ours: it passes the known function to the book definition on the input bytes.
`frontx_hof_entry g` specialises, compiles and adds `g.prog`/`g.exec` (SpecHof.lean). Nothing is proved by hand. -/
import Riscv.Frontx.SpecHof

namespace Proven.Frontx.BookS2
open Proven Proven.Frontx

/-! ## `MonadTransformers/Do.lean:93-102`: `EarlyReturn.Non.List.find?` -/

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

/-! ## `MonadTransformers/Do.lean:105-109`: `EarlyReturn.List.find?` (`do`, `failure`, `return`) -/

def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    find? p xs

end EarlyReturn

/-- `EarlyReturn.Non.List.find? (· > 3)` on the input -/
def nonFindGt3 (xs : ByteArray) : Option UInt8 := EarlyReturn.Non.List.find? (· > 3) xs.data.toList
frontx_hof_entry nonFindGt3

/-- `EarlyReturn.List.find? (· > 3)` on the input -/
def findGt3 (xs : ByteArray) : Option UInt8 := EarlyReturn.List.find? (· > 3) xs.data.toList
frontx_hof_entry findGt3

/-! ## `ProgramsProofs/Arrays.lean:293-306`: `findHelper`, `Array.find` -/

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

/-- `Array.find · (· > 3)` on the input bytes -/
def arrFindGt3 (xs : ByteArray) : Option (Nat × UInt8) := Array.find xs.data (· > 3)
frontx_hof_entry arrFindGt3

end Proven.Frontx.BookS2
