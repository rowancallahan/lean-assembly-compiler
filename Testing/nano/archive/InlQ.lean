/- nano inliner stage, paged, with a SMALL loop body (branch nano-final).  Same data layout and the same state
meaning as close B's `Nano.IP.mn` (Nano/InlP.lean), but one `set!` per step and shared reads (`let`), so that the
loop body's code stays within the conditional-branch range that `optB` checks (`brOK`): close B's `mn` lowers to
4187 words (spill-all), which no register choice can accept.  Closing a def (`13 a`) takes three steps (`ph` = 1,
2, 3) instead of one step with three writes.  The step lemmas of `Nano/InlPProof.lean` hold for `mnQ` with the
same statements (`Nano/InlQProof.lean`), so `inlQ_eq` follows by close B's proof. -/
import Legacy.Nano.InlP

set_option linter.unusedSimpArgs false

namespace Nano.IP
open Nano

/-- the step kind: 0 copy, 1 first byte 13/14/15, 2 first byte, 3 arity byte (then 8, 9), 4 after 14, 5 after 15
(a def: read its start, then 10 reads its end), 6 after 15 (no such def), 7 second byte -/
def mdQ (b j ph m n rem : Nat) : Nat :=
  if 0 < rem then 0
  else if ph == 0 then (if b == 13 || b == 14 || b == 15 then 1 else 2)
  else if ph == 1 then
    (if m == 13 then 3 else if m == 14 then 4 else if m == 15 then (if j < n then 5 else 6) else 7)
  else if ph == 2 then 8 else if ph == 3 then 9 else 10

theorem mdQ_cases (b j ph m n rem : Nat) :
    (mdQ b j ph m n rem = 0 ∧ 0 < rem) ∨ (mdQ b j ph m n rem = 3 ∧ ph = 1) ∨ (mdQ b j ph m n rem = 5 ∧ ph = 1) ∨
    (mdQ b j ph m n rem = 8 ∧ ph = 2) ∨
    ((mdQ b j ph m n rem = 1 ∨ mdQ b j ph m n rem = 2 ∨ mdQ b j ph m n rem = 4 ∨ mdQ b j ph m n rem = 6 ∨
      mdQ b j ph m n rem = 7 ∨ mdQ b j ph m n rem = 9 ∨ mdQ b j ph m n rem = 10) ∧ rem = 0) := by
  unfold mdQ
  simp only [beq_iff_eq, Bool.or_eq_true]
  (repeat' split) <;> omega

set_option maxRecDepth 100000 in
/-- the main loop: one read of `src`, one read of `ob`, one `set!` per step (a step that changes nothing writes a
cell's own value) -/
def mnQ (ob : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs : Nat) : Array Nat :=
  if i < src.size then
    let b := (src.get! i).toNat
    let j := hi * 256 + b
    let md := mdQ b j ph m n rem
    let w1 := if w < WCAP then w + 1 else w
    if md == 1 || md == 4 || md == 5 || md == 6 || md == 10 then
      let rd := ob[if md == 10 then j + 1 else j]!
      mnQ ob src (if md == 5 then i else i + 1) (if md == 1 then 1 else if md == 5 then 4 else 0)
        (if md == 1 then b else m) w n (if md == 4 then b else hi)
        (if md == 5 then (if rd < WCAP then rd else WCAP) else cp)
        (if md == 10 then (if rd - 1 - cp < WCAP then rd - 1 - cp else WCAP) else 0) cs
    else
      let rd := ob[BASE + cp]!
      mnQ (ob.set! (if md == 8 then (if n < 65536 then n + 1 else 65537) else if md == 9 then HD else BASE + w)
          (if md == 0 then rd else if md == 8 then w + 1 else if md == 9 then cs * 16777216 + w + 1 else b))
        src (if md == 0 || md == 3 || md == 8 then i else i + 1)
        (if md == 0 then ph else if md == 2 then 1 else if md == 3 then 2 else if md == 8 then 3 else 0)
        (if md == 2 then b else m) (if md == 3 || md == 8 then w else w1) (if md == 9 then n + 1 else n) hi
        (if md == 0 then cp + 1 else cp) (if md == 0 then rem - 1 else 0) (if md == 9 then w1 else cs)
  else ob
termination_by (src.size - i) * (5 * WCAP + 5) + 5 * rem + (4 - ph)
decreasing_by
  all_goals
    have hc := mdQ_cases (src.get! i).toNat (hi * 256 + (src.get! i).toNat) ph m n rem
    simp only [WCAP] at *
    rcases hc with ⟨hm, h⟩ | ⟨hm, rfl⟩ | ⟨hm, rfl⟩ | ⟨hm, rfl⟩ | ⟨h, rfl⟩
    · simp (config := {decide := true}) only [hm, if_true, dite_true, if_false, dite_false, Bool.or_eq_true, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, beq_self_eq_true]; omega
    · simp (config := {decide := true}) only [hm, if_true, dite_true, if_false, dite_false, Bool.or_eq_true, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, beq_self_eq_true]; omega
    · simp (config := {decide := true}) only [hm, if_true, dite_true, if_false, dite_false, Bool.or_eq_true, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, beq_self_eq_true]; omega
    · simp (config := {decide := true}) only [hm, if_true, dite_true, if_false, dite_false, Bool.or_eq_true, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, beq_self_eq_true]; omega
    · rcases h with hm | hm | hm | hm | hm | hm | hm <;> simp (config := {decide := true}) only [hm, if_true, dite_true, if_false, dite_false, Bool.or_eq_true, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, beq_self_eq_true] <;> (try split) <;> omega

/-- **the inliner stage** (small loop body) -/
def inlQ (xs : ByteArray) : Array UInt8 :=
  let ob := mnQ (Array.replicate (CAP + 0 * xs.size) 0) xs 0 0 0 0 0 0 0 0 0
  let ls := ob[HD]! / 16777216 % 16777216
  let le := ob[HD]! % 16777216
  let len := (le - 1 - ls) % 262144
  let k := if le == 0 then 0 else ob[BASE + (le - 1)]! % 256
  em (Array.replicate (20 * k + len + 38) 0) ob 0 ls len k

end Nano.IP
