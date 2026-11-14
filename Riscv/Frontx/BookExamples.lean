/- Functions of "Functional Programming in Lean" over `Nat` and `Bool` (survey verdict "B" on branch `booksurvey`),
with the book's own definitions, compiled by `frontx_compile`.  A `Nat` is one 64-bit variable: every generated
theorem has the hypothesis `n < 2^64` for each `Nat` parameter (in `f.Rep` / `f.Rep0`) and states
`result variable = BitVec.ofNat 64 (f args)`.

How each recursion is handled (all automatic):
* no recursion (`add1`, `maximum`, `isZero`, `pred`, `Nat.double`, `triple`, `quadruple`): one pass, `fun_cases`;
* `match k with | 0 => b | k' + 1 => E[f … k']`, the call not in tail position (`even`, `plus`, `times`, `minus`,
  `double`): the loop counting up, by `natRec_forIn` (`For.lean`), no accumulator algebra needed;
* `f x = g + f x'` under tests (`div`, `halve`): an accumulator is introduced; `f.runs` is stated for
  `acc + f x` and proved by `fun_induction` + `omega`.
Human input: the two equations `plus_eq`, `pred_eq` (a call to another recursive function is replaced by its closed
form; there are no calls yet) and the invariant `acc ≤ n` of `minus`. -/
import Riscv.Frontx.Translate

namespace Proven.Frontx.Book
open Proven Proven.Frontx

-- Functional Programming in Lean, Examples/Intro.lean (definitions as in the book)
def add1 (n : Nat) : Nat := n + 1
def maximum (n : Nat) (k : Nat) : Nat := if n < k then k else n
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false
def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')
def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')
def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')
def double (n : Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ k => double k + 2
def Nat.double (x : Nat) : Nat := x + x
def triple (x : Nat) : Nat := x + x + x
def quadruple (x : Nat) : Nat := x + x + x + x

frontx_compile add1
frontx_compile maximum
frontx_compile isZero
frontx_compile pred
frontx_compile Nat.double
frontx_compile triple
frontx_compile quadruple
frontx_compile even
frontx_compile plus
frontx_compile double
theorem plus_eq (n k : Nat) : plus n k = n + k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [plus, ih]; omega
theorem pred_eq (n : Nat) : pred n = n - 1 := by cases n <;> rfl
frontx_compile times using plus_eq
frontx_compile minus with (fun n _ _ acc => acc ≤ n) using pred_eq

/-- the book's `div` (Examples/ProgramsProofs/Div.lean): the bound is a hypothesis in the signature -/
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then 0
  else 1 + div (n - k) k ok
termination_by n
decreasing_by omega

def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1

frontx_compile div
frontx_compile halve

end Proven.Frontx.Book
