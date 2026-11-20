import Legacy.Nano.InlP
import Legacy.Nano.PgStage
import Legacy.Riscv.Frontx.WpBridge
import Legacy.Nano.WpSpill
namespace Nano.Mic
open Proven Proven.WA Proven.WP Proven.Top.Alloc
-- 1: UInt64 array, set!, small
def f1 (ob : Array UInt64) (src : ByteArray) (i : Nat) : Array UInt64 :=
  if i < src.size then f1 (ob.set! i (UInt64.ofNat i)) src (i + 1) else ob
termination_by src.size - i
def g1 (xs : ByteArray) : Array UInt64 := f1 (Array.replicate (64 + 0 * xs.size) 0) xs 0
set_option maxHeartbeats 0 in
wp_compileS g1 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i : Nat) => ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576
  measure fun (_ob : Array UInt64) (src : ByteArray) (i : Nat) => src.size - i
-- 2: same with 65600
def g2 (xs : ByteArray) : Array UInt64 := f1 (Array.replicate (65600 + 0 * xs.size) 0) xs 0
set_option maxHeartbeats 0 in
wp_compileS g2 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i : Nat) => ob.size = 65600 ∧ i ≤ src.size ∧ src.size ≤ 1048576
  measure fun (_ob : Array UInt64) (src : ByteArray) (i : Nat) => src.size - i
-- 3: read toNat, `if 0 < rem`
def f3 (ob : Array UInt64) (src : ByteArray) (i rem : Nat) : Array UInt64 :=
  if i < src.size then
    let rd := ob[i]!.toNat % 1024
    f3 (ob.set! i (if 0 < rem then ob[i]! else UInt64.ofNat i)) src (if 0 < rem then i else i + 1)
      (if 0 < rem then rem - 1 else rd % 16) else ob
termination_by (src.size - i) * 32 + rem
decreasing_by all_goals (repeat' split) <;> omega
def g3 (xs : ByteArray) : Array UInt64 := f3 (Array.replicate (64 + 0 * xs.size) 0) xs 0 0
set_option maxHeartbeats 0 in
wp_compileS g3 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i rem : Nat) => ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ rem < 32
  measure fun (_ob : Array UInt64) (src : ByteArray) (i rem : Nat) => (src.size - i) * 32 + rem
end Nano.Mic
