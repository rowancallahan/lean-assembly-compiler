import Legacy.Nano.InlP
import Legacy.Nano.PgStage
import Legacy.Riscv.Frontx.WpBridge
import Legacy.Nano.WpSpill
set_option linter.unusedSimpArgs false

namespace Nano.IRs
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
         else UInt64.ofNat (cs * 1048576 + (w - cs))))
      src (if 0 < rem then i else i + 3) (if 0 < rem || op == 0 then w + 1 else w)
      (if 0 < rem then cs else if op == 3 then w else cs)
      (if 0 < rem then cp + 1 else if op == 1 then rd / 1048576 else cp)
      (if 0 < rem then rem - 1 else if op == 1 then rd % 1048576 - 1 else 0)
  else ob
termination_by (src.size - i) * 1048576 + rem
decreasing_by
  all_goals
    by_cases hr : 0 < rem
    · simp only [hr, if_true, decide_true, Bool.true_or, dite_true]; omega
    · simp only [hr, if_false, decide_false, Bool.false_or, dite_false]
      (repeat' split) <;> omega

/-- the emit loop: copies cells `BASE + ls …` to bytes -/
def eq (out : Array UInt8) (ob : Array UInt64) (t ls len : Nat) : Array UInt8 :=
  if t < len then eq (out.set! t ob[BASE + ls + t]!.toUInt8) ob (t + 1) ls len else out
termination_by len - t

/-- **the paged stage `Q`** -/
def inlQ (xs : ByteArray) : Array UInt8 :=
  let ob := mq (Array.replicate (65600 + 0 * xs.size) 0) xs 0 0 0 0 0
  let h := ob[HD]!.toNat % 4611686018427387904
  eq (Array.replicate (h % 1048576) 0) ob 0 (h / 1048576 % 1099511627776) (h % 1048576)


open Proven Proven.WA Proven.WP Proven.Top.Alloc Nano.IP

def onlyE (xs : ByteArray) : Array UInt8 :=
  let h := xs.size
  eq (Array.replicate (h % 1048576) 0) (Array.replicate (65600 + 0 * xs.size) 0) 0 (h / 1048576 % 1099511627776) (h % 1048576)
set_option maxHeartbeats 0 in
wp_compileS onlyE max 1048576
  invariant fun (out : Array UInt8) (_ob : Array UInt64) (t ls len : Nat) =>
    out.size = len ∧ t ≤ len ∧ ls < 2 ^ 40 ∧ len < 1048576
  measure fun (_out : Array UInt8) (_ob : Array UInt64) (t _ls len : Nat) => len - t
end Nano.IRs
