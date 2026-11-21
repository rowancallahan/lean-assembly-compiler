/- The inliner's first stage `P` and last stage `W` (list stages, branch nano-final); the paged middle stage `Q` is
`Nano/InlR.lean`.

`P`: the byte records of `serU` (pairs `[m, x]`) to `Q`'s 3-byte records, resolving in scalars what needs no
table: the high callee byte `hi` (`14 h`), whether a callee exists (`hi * 256 + l < n`, `n` = closed defs), and the
def number of each closed def.  `[m, x]` (plain) ↦ `[0,0,m] [0,0,x]`; `[13, a]` ↦ `[0,0,a] [2, n/256, n%256] [3,0,0]`
(the table record only for `n < 65536`); `[14, h]` ↦ nothing; `[15, l]` ↦ `[1, hi, l]` if the callee exists.

`W`: `Q`'s output `a :: body` (or `[]`) to `wrap a body` (or `wrap 0 []`). -/
import Legacy.Nano.SerU

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
      (if hi.toUInt64 * 256 + x.toUInt64 < n then 1 :: hi :: x :: pr rest hi n else pr rest hi n)
    else 0 :: 0 :: m :: 0 :: 0 :: x :: pr rest hi n
  | _, _, _ => []

/-- stage `W`, at most 4 bytes per step: `ph` 0 reads the arity `k`, 1 emits `k` copies of `sArg` (5 steps of 4 bytes,
step `q`), 2 copies the body, 3 emits `mo 7 0 ++ sWr ++ mo 12 0` (9 steps of 4 bytes, step `q`) -/
def ww (xs : List UInt8) (ph k q : Nat) : List UInt8 :=
  if ph < 1 then
    match xs with
    | [] => 0 :: 0 :: ww [] 3 0 0
    | b :: t => if 256 ≤ b.toNat then [] else 0 :: 0 :: ww t 1 b.toNat 0
  else if ph < 2 then
    if k < 1 then ww xs 2 0 0
    else if q < 4 then
      (if q == 0 then 1 else 2) :: (if q == 0 then 0 else if q == 1 then 5 else if q == 2 then 3 else 1) :: 2 ::
        (if q == 0 then 6 else if q == 1 then 4 else if q == 2 then 2 else 0) :: ww xs 1 k (q + 1)
    else 3 :: 0 :: 4 :: 0 :: ww xs 1 (k - 1) 0
  else if ph < 3 then
    match xs with
    | [] => ww [] 3 0 0
    | b :: t => b :: ww t 2 0 0
  else
    if q < 8 then
      (if q == 0 then 7 else 11) ::
        (if q < 4 then (if q == 0 then 0 else if q == 1 then 0 else if q == 2 then 1 else 2)
         else (if q == 4 then 3 else if q == 5 then 4 else if q == 6 then 5 else 6)) :: 10 ::
        (if q < 4 then (if q == 0 then 0 else if q == 1 then 8 else if q == 2 then 16 else 24)
         else (if q == 4 then 32 else if q == 5 then 40 else if q == 6 then 48 else 56)) :: ww xs 3 0 (q + 1)
    else 11 :: 7 :: 12 :: 0 :: []
termination_by 4096 * xs.length + 1024 * (3 - ph) + 10 * k + (9 - q)
decreasing_by
  all_goals
    (try simp only [List.length_cons, List.length_nil] at *)
    omega

end Nano.IR
