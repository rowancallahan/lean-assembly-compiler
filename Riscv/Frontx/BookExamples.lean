/- Functions of "Functional Programming in Lean" over `Nat` and `Bool` (survey verdict "B" on branch `booksurvey`),
with the book's own definitions, compiled by `frontx_compile`.  A `Nat` is one 64-bit variable: every generated
theorem has the hypothesis `n < 2^64` for each `Nat` parameter (in `f.Rep` / `f.Rep0`) and states
`result variable = BitVec.ofNat 64 (f args)`.

How each recursion is handled (all automatic):
* no recursion (`add1`, `maximum`, `isZero`, `pred`, `Nat.double`, `triple`, `quadruple`, `timesTwelve`): one pass, `fun_cases`;
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
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)

frontx_compile add1
frontx_compile maximum
frontx_compile isZero
frontx_compile pred
frontx_compile Nat.double
-- multiplication by a literal: shifts and adds, through a generated equation `mulLitL_c` (proved by `omega`)
frontx_compile NewNamespace.triple
frontx_compile NewNamespace.quadruple
frontx_compile timesTwelve
frontx_compile even
frontx_compile plus
frontx_compile double
theorem plus_eq (n k : Nat) : plus n k = n + k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [plus, ih]; omega
theorem pred_eq (n : Nat) : pred n = n - 1 := by cases n <;> rfl
frontx_compile times using plus_eq
-- `pred` is called (its program inlined as a sub-program, `Tree.sub`); no closed form.  The invariant `acc ≤ n`
-- is still needed: `pred`'s argument must be `< 2^64` (`pred x ≤ n` is proved by unfolding `pred` in the obligation)
frontx_compile minus with (fun n _ _ acc => acc ≤ n)

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

/-! ## Entry points: the arguments are 16-bit little-endian numbers in the input bytes

`fAt xs i := f (u16 xs i) …` calls the compiled `f` (a recursive `f` is a call: its program runs as a sub-program
of `fAt`'s, `Tree.sub`; a non-recursive one is inlined); `fE xs := fAt xs 0` is the entry point. -/

/-- byte `i` of the input, `0` past the end -/
@[inline] def byteAt (xs : ByteArray) (i : Nat) : UInt8 := if h : i < xs.size then xs[i] else 0
/-- the 16-bit little-endian number at byte `i` -/
def u16 (xs : ByteArray) (i : Nat) : Nat := (byteAt xs i).toNat + 256 * (byteAt xs (i + 1)).toNat

def add1At (xs : ByteArray) (i : Nat) : Nat := add1 (u16 xs i)
def maximumAt (xs : ByteArray) (i : Nat) : Nat := maximum (u16 xs i) (u16 xs (i + 2))
def isZeroAt (xs : ByteArray) (i : Nat) : Bool := isZero (u16 xs i)
def predAt (xs : ByteArray) (i : Nat) : Nat := pred (u16 xs i)
def evenAt (xs : ByteArray) (i : Nat) : Bool := even (u16 xs i)
def plusAt (xs : ByteArray) (i : Nat) : Nat := plus (u16 xs i) (u16 xs (i + 2))
def timesAt (xs : ByteArray) (i : Nat) : Nat := times (u16 xs i) (u16 xs (i + 2))
def minusAt (xs : ByteArray) (i : Nat) : Nat := minus (u16 xs i) (u16 xs (i + 2))
def doubleAt (xs : ByteArray) (i : Nat) : Nat := double (u16 xs i)
def natDoubleAt (xs : ByteArray) (i : Nat) : Nat := Nat.double (u16 xs i)
def tripleAt (xs : ByteArray) (i : Nat) : Nat := NewNamespace.triple (u16 xs i)
def quadrupleAt (xs : ByteArray) (i : Nat) : Nat := NewNamespace.quadruple (u16 xs i)
def timesTwelveAt (xs : ByteArray) (i : Nat) : Nat := timesTwelve (u16 xs i)
/-- the divisor is `u16 + 1` (the book's `div` takes the proof `k ≠ 0`) -/
def divAt (xs : ByteArray) (i : Nat) : Nat := div (u16 xs i) (u16 xs (i + 2) + 1) (Nat.succ_ne_zero _)
def halveAt (xs : ByteArray) (i : Nat) : Nat := halve (u16 xs i)

frontx_compile add1At requires fun _ i => i + 8 < 2 ^ 64
frontx_compile maximumAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile isZeroAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile predAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile evenAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile plusAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile timesAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile minusAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile doubleAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile natDoubleAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile tripleAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile quadrupleAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile timesTwelveAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile divAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile halveAt requires fun _ i => i + 8 < 2 ^ 64

end Proven.Frontx.Book
