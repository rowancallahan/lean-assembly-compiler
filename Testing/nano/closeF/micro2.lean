import Legacy.Nano.InlP
import Legacy.Nano.PgStage
import Legacy.Riscv.Frontx.WpBridge
import Legacy.Nano.WpSpill
namespace Nano.Mic
open Proven Proven.WA Proven.WP Proven.Top.Alloc
open Nano.IP
def mq4 (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) : Array UInt64 :=
  if i + 2 < src.size then
    let op := (src.get! i).toNat
    let x := (src.get! (i + 1)).toNat * 256 + (src.get! (i + 2)).toNat
    let rv := ob[if 0 < rem then BASE + cp else x]!
    let rd := rv.toNat % 4611686018427387904
    mq4 (ob.set! (if 0 < rem || op == 0 then BASE + w else if op == 3 then HD else x)
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

def g4 (xs : ByteArray) : Array UInt64 := mq4 (Array.replicate (64 + 0 * xs.size) 0) xs 0 0 0 0 0
set_option maxHeartbeats 0 in
wp_compileS g4 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) =>
    ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ w + (src.size - i) * 1048576 + rem ≤ 2 ^ 41 ∧
      cs ≤ w ∧ cp + rem ≤ 2 ^ 45
  measure fun (_ob : Array UInt64) (src : ByteArray) (i _w _cs _cp rem : Nat) => (src.size - i) * 1048576 + rem
def mq5 (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) : Array UInt64 :=
  if i + 2 < src.size then
    let op := (src.get! i).toNat
    let x := (src.get! (i + 1)).toNat
    let rv := ob[if 0 < rem then BASE + cp else x]!
    let rd := rv.toNat % 4611686018427387904
    mq5 (ob.set! (if 0 < rem || op == 0 then BASE + w else if op == 3 then HD else x)
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

def g5 (xs : ByteArray) : Array UInt64 := mq5 (Array.replicate (64 + 0 * xs.size) 0) xs 0 0 0 0 0
set_option maxHeartbeats 0 in
wp_compileS g5 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) =>
    ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ w + (src.size - i) * 1048576 + rem ≤ 2 ^ 41 ∧
      cs ≤ w ∧ cp + rem ≤ 2 ^ 45
  measure fun (_ob : Array UInt64) (src : ByteArray) (i _w _cs _cp rem : Nat) => (src.size - i) * 1048576 + rem
def mq6 (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) : Array UInt64 :=
  if i + 2 < src.size then
    let op := (src.get! i).toNat
    let x := (src.get! (i + 1)).toNat * 256 + (src.get! (i + 2)).toNat
    let rv := ob[if 0 < rem then BASE + cp else x]!
    let rd := rv.toNat % 4611686018427387904
    mq6 (ob.set! (if 0 < rem || op == 0 then BASE + w else if op == 3 then HD else x)
        (if 0 < rem || op == 1 then rv else if op == 0 then UInt64.ofNat x
         else UInt64.ofNat (cs * 1048576 + (w - cs))))
      src (if 0 < rem then i else i + 3) (if 0 < rem || op == 0 then w + 1 else w)
      cs
      cp
      (if 0 < rem then rem - 1 else 0)
  else ob
termination_by (src.size - i) * 1048576 + rem
decreasing_by
  all_goals
    by_cases hr : 0 < rem
    · simp only [hr, if_true, decide_true, Bool.true_or, dite_true]; omega
    · simp only [hr, if_false, decide_false, Bool.false_or, dite_false]
      (repeat' split) <;> omega

def g6 (xs : ByteArray) : Array UInt64 := mq6 (Array.replicate (64 + 0 * xs.size) 0) xs 0 0 0 0 0
set_option maxHeartbeats 0 in
wp_compileS g6 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) =>
    ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ w + (src.size - i) * 1048576 + rem ≤ 2 ^ 41 ∧
      cs ≤ w ∧ cp + rem ≤ 2 ^ 45
  measure fun (_ob : Array UInt64) (src : ByteArray) (i _w _cs _cp rem : Nat) => (src.size - i) * 1048576 + rem
def mq7 (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) : Array UInt64 :=
  if i + 2 < src.size then
    let op := (src.get! i).toNat
    let x := (src.get! (i + 1)).toNat * 256 + (src.get! (i + 2)).toNat
    let rv := ob[if 0 < rem then BASE + cp else x]!
    let rd := rv.toNat % 4611686018427387904
    mq7 (ob.set! (BASE + w) rv)
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

def g7 (xs : ByteArray) : Array UInt64 := mq7 (Array.replicate (64 + 0 * xs.size) 0) xs 0 0 0 0 0
set_option maxHeartbeats 0 in
wp_compileS g7 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) =>
    ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ w + (src.size - i) * 1048576 + rem ≤ 2 ^ 41 ∧
      cs ≤ w ∧ cp + rem ≤ 2 ^ 45
  measure fun (_ob : Array UInt64) (src : ByteArray) (i _w _cs _cp rem : Nat) => (src.size - i) * 1048576 + rem
end Nano.Mic
