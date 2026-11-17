/- The inliner's first stage `P` and last stage `W` (list stages, branch nano-final); the paged middle stage `Q` is
`Nano/InlR.lean`.

`P`: the byte records of `serU` (pairs `[m, x]`) to `Q`'s 3-byte records, resolving in scalars what needs no
table: the high callee byte `hi` (`14 h`), whether a callee exists (`hi * 256 + l < n`, `n` = closed defs), and the
def number of each closed def.  `[m, x]` (plain) ↦ `[0,0,m] [0,0,x]`; `[13, a]` ↦ `[0,0,a] [2, n/256, n%256] [3,0,0]`
(the table record only for `n < 65536`); `[14, h]` ↦ nothing; `[15, l]` ↦ `[1, hi, l]` if the callee exists.

`W`: `Q`'s output `a :: body` (or `[]`) to `wrap a body` (or `wrap 0 []`). -/
import Nano.SerU

namespace Nano.IR
open Nano Nano.U

/-- stage `P` -/
def pr : List UInt8 → UInt8 → UInt64 → List UInt8
  | m :: x :: rest, hi, n =>
    if m == 13 then
      (if n < 65536 then 0 :: 0 :: x :: 2 :: (n >>> 8).toUInt8 :: n.toUInt8 :: 3 :: 0 :: 0 :: pr rest hi (n + 1)
       else 0 :: 0 :: x :: 3 :: 0 :: 0 :: pr rest hi (n + 1))
    else if m == 14 then pr rest x n
    else if m == 15 then
      (if (hi.toUInt64 <<< 8) ||| x.toUInt64 < n then 1 :: hi :: x :: pr rest hi n else pr rest hi n)
    else 0 :: 0 :: m :: 0 :: 0 :: x :: pr rest hi n
  | _, _, _ => []

theorem u8_pred (k : UInt8) (h : ¬ k = 0) : (k - 1).toNat < k.toNat := by
  have h2 : k.toNat ≠ 0 := fun e => h (UInt8.toNat_inj.mp (by simpa using e))
  rw [UInt8.toNat_sub_of_le]
  · simp; omega
  · rw [UInt8.le_iff_toNat_le]; simp; omega

/-- stage `W`: `ph` 0 reads the arity, 1 emits the prologue (`k` copies of `sArg`), 2 copies the body -/
def ww (xs : List UInt8) (ph : Nat) (k : UInt8) : List UInt8 :=
  match xs with
  | [] =>
    if ph == 2 then 7 :: 0 :: 10 :: 0 :: 11 :: 0 :: 10 :: 8 :: 11 :: 1 :: 10 :: 16 :: 11 :: 2 :: 10 :: 24 :: 11 :: 3 ::
      10 :: 32 :: 11 :: 4 :: 10 :: 40 :: 11 :: 5 :: 10 :: 48 :: 11 :: 6 :: 10 :: 56 :: 11 :: 7 :: 12 :: 0 :: []
    else if ph == 0 then 0 :: 0 :: 7 :: 0 :: 10 :: 0 :: 11 :: 0 :: 10 :: 8 :: 11 :: 1 :: 10 :: 16 :: 11 :: 2 :: 10 :: 24 ::
      11 :: 3 :: 10 :: 32 :: 11 :: 4 :: 10 :: 40 :: 11 :: 5 :: 10 :: 48 :: 11 :: 6 :: 10 :: 56 :: 11 :: 7 :: 12 :: 0 :: []
    else if k == 0 then ww [] 2 k
    else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 :: ww [] 1 (k - 1)
  | b :: t =>
    if ph == 2 then b :: ww t 2 k
    else if ph == 0 then 0 :: 0 :: ww t 1 b
    else if k == 0 then ww (b :: t) 2 k
    else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 ::
      ww (b :: t) 1 (k - 1)
termination_by 1024 * xs.length + 512 * (if ph == 2 then 0 else if ph == 0 then 2 else 1) + k.toNat
decreasing_by
  all_goals
    simp_all (config := {decide := true}) only [List.length_cons, List.length_nil, beq_iff_eq, if_true, if_false]
    all_goals first
      | omega
      | (have := u8_pred k ‹_›; omega)
      | (have := UInt8.toNat_lt_size ‹UInt8›; simp only [UInt8.size] at *; omega)

end Nano.IR
