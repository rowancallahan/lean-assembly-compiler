/- List functions of "Functional Programming in Lean" that consume a list and return a number (survey class "B",
`Testing/notes/book_survey.csv` on branch `booksurvey`).  The definitions are the book's (transcribed; signatures
as in the survey).  For each: `frontx_view f` (the list is the input block from an index on; type parameters
become `UInt8`; `List Nat` reads the bytes as numbers), then `frontx_compile f.view from f.view.eq measure …`.
Nothing in this file is proved by hand except the one-line entry equations (`rfl`). -/
import Riscv.Frontx.Translate

namespace Proven.Frontx.BookList
open Proven Proven.Frontx

/-! ## `length` (1 Getting to Know Lean) -/

namespace Explicit
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length α ys)
frontx_view length
frontx_compile length.view from length.view.eq measure fun B i => B.size - i
end Explicit

namespace BetterPlicity
def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length ys)
frontx_view length
frontx_compile length.view from length.view.eq measure fun B i => B.size - i
end BetterPlicity

namespace AutoImpl
def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)
frontx_view length
frontx_compile length.view from length.view.eq measure fun B i => B.size - i
end AutoImpl

namespace MatchDef
def length : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (length ys)
frontx_view length
frontx_compile length.view from length.view.eq measure fun B i => B.size - i
end MatchDef

/-! ## 9 Programming, Proving, Performance (`TCO.lean`) -/

namespace NonTail
def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
frontx_view sum
frontx_compile sum.view from sum.view.eq measure fun B i => B.size - i

def length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1
frontx_view length
frontx_compile length.view from length.view.eq measure fun B i => B.size - i
end NonTail

namespace Tail
def sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs
def sum (xs : List Nat) : Nat := Tail.sumHelper 0 xs
frontx_view sumHelper
-- the running sum stays below 2^64: at most 255 per remaining byte
frontx_compile sumHelper.view from sumHelper.view.eq measure (fun B i _ => B.size - i)
  with fun B i soFar => i ≤ B.size ∧ soFar + 255 * (B.size - i) < 2 ^ 64

def lengthHelper (soFar : Nat) : List α → Nat
  | [] => soFar
  | _ :: xs => lengthHelper (soFar + 1) xs
def length (xs : List α) : Nat := Tail.lengthHelper 0 xs
frontx_view lengthHelper
frontx_compile lengthHelper.view from lengthHelper.view.eq measure (fun B i _ => B.size - i)
  with fun B i soFar => i ≤ B.size ∧ soFar + (B.size - i) < 2 ^ 64
end Tail

/-! ## `Option` results (1 Getting to Know Lean) -/

namespace Floop
def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y
frontx_view List.head?
frontx_compile List.head?.view from List.head?.view.eq measure fun _ _ => 0
end Floop

def _root_.List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | y :: ys => if predicate y then some y else ys.findFirst? predicate

/-- specialisation of the polymorphic, higher-order `findFirst?` (`α := UInt8`, `predicate := (· > 3)`):
`frontx_spec` proves `findGt3.eq` (the body with the recursive call folded) from the book's equation -/
def findGt3 (xs : List UInt8) : Option UInt8 := xs.findFirst? (· > 3)
frontx_spec findGt3
frontx_view findGt3 from findGt3.eq
frontx_compile findGt3.view from findGt3.view.eq measure fun B i => B.size - i

/-! ## Entry points: the book functions on the input bytes -/

def tailSum (xs : ByteArray) : Nat := Tail.sum (xs.data.toList.map UInt8.toNat)
theorem tailSum_eq (xs : ByteArray) : tailSum xs = Tail.sumHelper.view xs 0 0 := rfl
frontx_entry tailSum from tailSum_eq

def nonTailSum (xs : ByteArray) : Nat := NonTail.sum (xs.data.toList.map UInt8.toNat)
theorem nonTailSum_eq (xs : ByteArray) : nonTailSum xs = NonTail.sum.view xs 0 := rfl
frontx_entry nonTailSum from nonTailSum_eq

def tailLength (xs : ByteArray) : Nat := Tail.length xs.data.toList
theorem tailLength_eq (xs : ByteArray) : tailLength xs = Tail.lengthHelper.view xs 0 0 := rfl
frontx_entry tailLength from tailLength_eq

def bookLength (xs : ByteArray) : Nat := MatchDef.length xs.data.toList
theorem bookLength_eq (xs : ByteArray) : bookLength xs = MatchDef.length.view xs 0 := rfl
frontx_entry bookLength from bookLength_eq

end Proven.Frontx.BookList
