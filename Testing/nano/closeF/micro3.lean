import Nano.InlP
import Nano.PgStage
import Riscv.Frontx.WpBridge
import Nano.WpSpill
namespace Nano.Mic
open Proven Proven.WA Proven.WP Proven.Top.Alloc
-- 8: guard i + 2 < size, 3 reads
def f8 (ob : Array UInt64) (src : ByteArray) (i rem : Nat) : Array UInt64 :=
  if i + 2 < src.size then
    let x := (src.get! (i + 1)).toNat * 256 + (src.get! (i + 2)).toNat
    f8 (ob.set! i (if 0 < rem then ob[i]! else UInt64.ofNat x)) src (if 0 < rem then i else i + 3)
      (if 0 < rem then rem - 1 else x % 16) else ob
termination_by (src.size - i) * 32 + rem
decreasing_by all_goals (repeat' split) <;> omega
def g8 (xs : ByteArray) : Array UInt64 := f8 (Array.replicate (64 + 0 * xs.size) 0) xs 0 0
set_option maxHeartbeats 0 in
wp_compileS g8 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i rem : Nat) => ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ rem < 32
  measure fun (_ob : Array UInt64) (src : ByteArray) (i rem : Nat) => (src.size - i) * 32 + rem
-- 9: `||`
def f9 (ob : Array UInt64) (src : ByteArray) (i rem : Nat) : Array UInt64 :=
  if i < src.size then
    let op := (src.get! i).toNat
    f9 (ob.set! i (if 0 < rem || op == 0 then ob[i]! else UInt64.ofNat i)) src (if 0 < rem then i else i + 1)
      (if 0 < rem then rem - 1 else op % 16) else ob
termination_by (src.size - i) * 32 + rem
decreasing_by all_goals (repeat' split) <;> omega
def g9 (xs : ByteArray) : Array UInt64 := f9 (Array.replicate (64 + 0 * xs.size) 0) xs 0 0
set_option maxHeartbeats 0 in
wp_compileS g9 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i rem : Nat) => ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ rem < 32
  measure fun (_ob : Array UInt64) (src : ByteArray) (i rem : Nat) => (src.size - i) * 32 + rem
-- 10: big multiplier invariant
def f10 (ob : Array UInt64) (src : ByteArray) (i w rem : Nat) : Array UInt64 :=
  if i < src.size then
    f10 (ob.set! i (if 0 < rem then ob[i]! else UInt64.ofNat i)) src (if 0 < rem then i else i + 1) (w + 1)
      (if 0 < rem then rem - 1 else (src.get! i).toNat % 16) else ob
termination_by (src.size - i) * 1048576 + rem
decreasing_by all_goals (repeat' split) <;> omega
def g10 (xs : ByteArray) : Array UInt64 := f10 (Array.replicate (64 + 0 * xs.size) 0) xs 0 0 0
set_option maxHeartbeats 0 in
wp_compileS g10 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i w rem : Nat) => ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ w + (src.size - i) * 1048576 + rem ≤ 2 ^ 41 ∧ rem < 32
  measure fun (_ob : Array UInt64) (src : ByteArray) (i _w rem : Nat) => (src.size - i) * 1048576 + rem
end Nano.Mic
