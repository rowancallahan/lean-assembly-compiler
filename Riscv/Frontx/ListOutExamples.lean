/- List functions of "Functional Programming in Lean" that RETURN a list (survey class "B"; definitions transcribed
from `leanprover/fp-lean`, `examples/Examples/Intro.lean` and `ProgramsProofs/TCO.lean`), compiled in list mode:
the result is written to the output block (heap block 1) from index `j` on, the length is returned.

Per function: `frontx_view f` (general `match` shapes: several discriminants, nested patterns), then
`frontx_compile f.view from f.view.eq measure …`; a function whose result can be the rest of the input
(`drop`, `append`) first gets `frontx_tailcopy f.view measure …` (the copy of the rest is a mode of the same
loop) and is compiled as `f.view.cp`.  The generated theorems: `f.view.exec` (source level) and, for the entry
points at the end, `g.exec` (the hypothesis of `implements1_list`).  Nothing is proved by hand except the
one-line entry equations (`rfl`). -/
import Riscv.Frontx.ListExamples

namespace Proven.Frontx.BookOut
open Proven Proven.Frontx

/-! ## `take`, `drop` (1 Getting to Know Lean) -/

def take (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | _, [] => []
  | Nat.zero, _ => []
  | Nat.succ n', x :: xs => x :: take n' xs
frontx_view take
frontx_compile take.view from take.view.eq measure fun B i _ => B.size - i

def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, x :: xs => drop n xs
frontx_view drop
frontx_tailcopy drop.view measure fun B i _ => B.size - i
frontx_compile drop.view.cp from drop.view.cp.eq measure drop.view.cp.μ

namespace Match
def drop (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys => ys
  | _, [] => []
  | Nat.succ n , y :: ys => drop n ys
frontx_view drop
frontx_tailcopy drop.view measure fun B i _ => B.size - i
frontx_compile drop.view.cp from drop.view.cp.eq measure drop.view.cp.μ
end Match

/-! ## `List.final?` (1, three patterns; an `Option` result: two variables) -/

namespace Floop
def List.final? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [y] => some y
  | y1 :: y2 :: ys => final? (y2::ys)
frontx_view List.final?
frontx_compile List.final?.view from List.final?.view.eq measure fun B i => B.size - i
end Floop

/-! ## `NonTail.filter` (9 Programming, Proving, Performance), specialised to `(· > 3)` -/

def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs
def filterGt3 (xs : List UInt8) : List UInt8 := NonTail.filter (· > 3) xs
frontx_spec filterGt3
frontx_view filterGt3 from filterGt3.eq
frontx_compile filterGt3.view from filterGt3.view.eq measure fun B i => B.size - i

/-! ## `List.map`, `List.append` (core definitions, as the book uses them) -/

def incAll (xs : List UInt8) : List UInt8 := List.map (· + 1) xs
frontx_spec incAll
frontx_view incAll from incAll.eq
frontx_compile incAll.view from incAll.view.eq measure fun B i => B.size - i

def append (xs ys : List UInt8) : List UInt8 := List.append xs ys
frontx_spec append
frontx_view append from append.eq
frontx_tailcopy append.view measure fun B i _ => B.size - i
frontx_compile append.view.cp from append.view.cp.eq measure append.view.cp.μ

/-! ## Entry points: the book functions on the input bytes -/

def take5 (xs : ByteArray) : List UInt8 := take 5 xs.data.toList
theorem take5_eq (xs : ByteArray) : take5 xs = take.view xs 0 5 := rfl
frontx_entry take5 from take5_eq

def drop5 (xs : ByteArray) : List UInt8 := drop 5 xs.data.toList
theorem drop5_eq (xs : ByteArray) : drop5 xs = drop.view.cp xs 0 5 false 0 := rfl
frontx_entry drop5 from drop5_eq

def matchDrop3 (xs : ByteArray) : List UInt8 := Match.drop 3 xs.data.toList
theorem matchDrop3_eq (xs : ByteArray) : matchDrop3 xs = Match.drop.view.cp xs 0 3 false 0 := rfl
frontx_entry matchDrop3 from matchDrop3_eq

def filterAll (xs : ByteArray) : List UInt8 := NonTail.filter (· > 3) xs.data.toList
theorem filterAll_eq (xs : ByteArray) : filterAll xs = filterGt3.view xs 0 := rfl
frontx_entry filterAll from filterAll_eq

def incEach (xs : ByteArray) : List UInt8 := List.map (· + 1) xs.data.toList
theorem incEach_eq (xs : ByteArray) : incEach xs = incAll.view xs 0 := rfl
frontx_entry incEach from incEach_eq

def twice (xs : ByteArray) : List UInt8 := xs.data.toList ++ xs.data.toList
theorem twice_eq (xs : ByteArray) : twice xs = append.view.cp xs 0 0 false 0 := rfl
frontx_entry twice from twice_eq

/-! ## Entry points with an `Option UInt8` result (two bytes: tag, payload) -/

def headOf (xs : ByteArray) : Option UInt8 := BookList.Floop.List.head? xs.data.toList
theorem headOf_eq (xs : ByteArray) : headOf xs = BookList.Floop.List.head?.view xs 0 := rfl
frontx_entry headOf from headOf_eq

def finalOf (xs : ByteArray) : Option UInt8 := Floop.List.final? xs.data.toList
theorem finalOf_eq (xs : ByteArray) : finalOf xs = Floop.List.final?.view xs 0 := rfl
frontx_entry finalOf from finalOf_eq

def findFirstGt3 (xs : ByteArray) : Option UInt8 := List.findFirst? xs.data.toList (· > 3)
theorem findFirstGt3_eq (xs : ByteArray) : findFirstGt3 xs = BookList.findGt3.view xs 0 := rfl
frontx_entry findFirstGt3 from findFirstGt3_eq

end Proven.Frontx.BookOut
