/- nano inliner, three stages (branch nano-final): `P` (list stage, `Nano/InlRP.lean`) turns the byte records of
`serU` into 3-byte records, `Q` (this file, paged) keeps the table, `W` (list stage) wraps the entry body.

`Q`'s records `[op, a, b]` (`x = a * 256 + b`): `op = 0`: append byte `x`; `1`: append the body of def `x` (copy
mode `cp`/`rem`); `2`: table cell `x` := the current body (`pk` = start · 2^17 + length, the length counting the
arity byte, below 2^17); `3`: header cell `HD` := the current body, the next body starts here.  One step = one record or one
copied byte; every step reads `ob` once and writes one cell (a call writes cell `x` its own value). -/
import Nano.InlP

set_option linter.unusedSimpArgs false

namespace Nano.IR
open Nano Nano.IP

/-- the paged loop (cells are `UInt64`, so every value read is below `2^64`) -/
def mq (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) : Array UInt64 :=
  if i + 2 < src.size then
    let op := (src.get! i).toNat
    let x := (src.get! (i + 1)).toNat * 256 + (src.get! (i + 2)).toNat
    let rv := ob[if 0 < rem then BASE + cp else x]!
    let rd := rv.toNat % 4611686018427387904
    mq (ob.set! (if 0 < rem || op == 0 then BASE + w else if op == 3 then HD else x)
        (if 0 < rem || op == 1 then rv else if op == 0 then UInt64.ofNat x
         else UInt64.ofNat (cs * 131072 + (w - cs))))
      src (if 0 < rem then i else i + 3) (if 0 < rem || op == 0 then w + 1 else w)
      (if 0 < rem then cs else if op == 3 then w else cs)
      (if 0 < rem then cp + 1 else if op == 1 then rd / 131072 else cp)
      (if 0 < rem then rem - 1 else if op == 1 then rd % 131072 - 1 else 0)
  else ob
termination_by (src.size - i) * 65536 + rem
decreasing_by
  all_goals
    by_cases hr : 0 < rem
    · simp only [hr, if_true, decide_true, Bool.true_or, dite_true]; omega
    · simp only [hr, if_false, decide_false, Bool.false_or, dite_false]
      (repeat' split) <;> omega

/-- the emit loop: the last cell `BASE + ls + len - 1` (the arity byte), then the cells `BASE + ls …` (the body) -/
def eq (out : Array UInt8) (ob : Array UInt64) (t ls len : Nat) : Array UInt8 :=
  if t < len then eq (out.set! t ob[BASE + ls + (if t == 0 then len else t) - 1]!.toUInt8) ob (t + 1) ls len else out
termination_by len - t

/-- **the paged stage `Q`** -/
def inlQ (xs : ByteArray) : Array UInt8 :=
  let ob := mq (Array.replicate (CAP + 0 * xs.size) 0) xs 0 0 0 0 0
  let h := ob[HD]!.toNat % 4611686018427387904
  eq (Array.replicate (h % 131072) 0) ob 0 (h / 131072 % 1099511627776) (h % 131072)

end Nano.IR
