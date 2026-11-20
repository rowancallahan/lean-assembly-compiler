/- The inliner machine, slim step (branch `nano-closeB`): `mn3` = `Nano.IP.mn` with the step's shared reads bound
by `let` and the array update chosen by `if` (no rewriting of unchanged cells), so the paged program is smaller.
`inlP3` = `inlP` with `mn3`.  Equal to `inlB` when the table fits: `inlP3_eq` (`Nano/InlP3Proof.lean`). -/
import Legacy.Nano.InlP

namespace Nano.IP
open Nano

def mn3 (ob : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs : Nat) : Array Nat :=
  if i < src.size then
    let b := (src.get! i).toNat
    let j := hi * 256 + b
    let a := ob[j]!
    let e := ob[j + 1]!
    let w1 := if w < WCAP then w + 1 else w
    mn3 (if 0 < rem then ob.set! (BASE + w) ob[BASE + cp]!
         else if ph == 1 && m == 13 then
           ((ob.set! (BASE + w) b).set! (if n < 65536 then n + 1 else 65537) (w + 1)).set! HD (cs * 16777216 + w + 1)
         else if (ph == 0 && !(b == 13 || b == 14 || b == 15)) || (ph == 1 && !(m == 14 || m == 15)) then
           ob.set! (BASE + w) b
         else ob)
       src
       (if 0 < rem then i else i + 1)
       (if 0 < rem then ph else if ph == 0 then 1 else 0)
       (if 0 < rem then m else if ph == 0 then b else m)
       (if 0 < rem then w1
        else if ph == 0 then (if b == 13 || b == 14 || b == 15 then w else w1)
        else if m == 14 || m == 15 then w else w1)
       (if 0 < rem then n else if ph == 1 && m == 13 then n + 1 else n)
       (if 0 < rem then hi else if ph == 1 && m == 14 then b else hi)
       (if 0 < rem then cp + 1 else if ph == 1 && m == 15 && j < n then (if a < WCAP then a else WCAP) else cp)
       (if 0 < rem then rem - 1
        else if ph == 1 && m == 15 && j < n then (if e - 1 - a < WCAP then e - 1 - a else WCAP) else 0)
       (if 0 < rem then cs else if ph == 1 && m == 13 then w1 else cs)
  else ob
termination_by (src.size - i) * (WCAP + 1) + rem
decreasing_by
  all_goals
    rename_i h
    simp only [WCAP] at *
    by_cases hr : 0 < rem
    · simp only [hr, dite_true]; omega
    · simp only [hr, dite_false, Nat.mul_zero, Nat.add_zero]
      split <;> (try split) <;> omega

def inlP3 (xs : ByteArray) : Array UInt8 :=
  let ob := mn3 (Array.replicate (CAP + 0 * xs.size) 0) xs 0 0 0 0 0 0 0 0 0
  let ls := ob[HD]! / 16777216 % 16777216
  let le := ob[HD]! % 16777216
  let len := (le - 1 - ls) % 262144
  let k := if le == 0 then 0 else ob[BASE + (le - 1)]! % 256
  em (Array.replicate (20 * k + len + 38) 0) ob 0 ls len k

end Nano.IP
