/- Calls to other translated functions (`Tree.sub`, `Sub.lean`): the callee's whole program runs inside the caller's
loop body, its variables renamed into a free range of the caller's and cleared afterwards.  A call to a recursive
(looping) function is a nested loop.  Here: a quadratic loop around the loop of `occursFrom`.  The book's `minus`
calling `pred` (no closed form) is in `BookExamples.lean`, the entry points of the `Nat` book functions (calls to
`plus`, `even`, `times`, `div`, …) in `BookExamples.lean` / `Machine.lean`. -/
import Riscv.Frontx.Translate

namespace Proven.Frontx.Calls
open Proven Proven.Frontx

/-- does `c` occur at or after `i` -/
def occursFrom (bs : ByteArray) (i : Nat) (c : UInt8) : Bool :=
  if h : i < bs.size then (if bs[i] == c then true else occursFrom bs (i + 1) c) else false
termination_by bs.size - i
frontx_compile occursFrom

/-- the number of positions `k` whose byte occurs again after `k`: a loop around the loop of `occursFrom` -/
def countDup (bs : ByteArray) (k acc : Nat) : Nat :=
  if h : k < bs.size then countDup bs (k + 1) (if occursFrom bs (k + 1) bs[k] then acc + 1 else acc) else acc
termination_by bs.size - k
frontx_compile countDup with fun _ k acc => acc ≤ k

def dupCount (xs : ByteArray) : Nat := countDup xs 0 0
frontx_entry dupCount

/-! ## Survey class "C": two list inputs (`sameLength`, 1 Getting to Know Lean, `Both` version)

Both lists are views of the input block with their own indices; the entry point compares the suffixes from `1` and
from `1 + xs[0]`. -/

namespace Both
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | _ :: xs', _ :: ys' => sameLength xs' ys'
  | _, _ => false
end Both
frontx_view Both.sameLength
frontx_compile Both.sameLength.view from Both.sameLength.view.eq measure fun B i _ => B.size - i

@[inline] def byteAt (xs : ByteArray) (i : Nat) : UInt8 := if h : i < xs.size then xs[i] else 0
def sameLenAt (xs : ByteArray) (i : Nat) : Bool := Both.sameLength.view xs (i + 1) (i + 1 + (byteAt xs i).toNat)
frontx_compile sameLenAt requires fun _ i => i + 300 < 2 ^ 64
def sameLen (xs : ByteArray) : Bool := sameLenAt xs 0
frontx_entry sameLen

end Proven.Frontx.Calls
