import Nano.InlP
import Nano.PgStage
import Riscv.Frontx.WpBridge
import Nano.WpSpill
namespace Nano.Mic
open Proven Proven.WA Proven.WP Proven.Top.Alloc
-- 10: big multiplier invariant
def f10_4096 (ob : Array UInt64) (src : ByteArray) (i w rem : Nat) : Array UInt64 :=
  if i < src.size then
    f10_4096 (ob.set! i (if 0 < rem then ob[i]! else UInt64.ofNat i)) src (if 0 < rem then i else i + 1) (w + 1)
      (if 0 < rem then rem - 1 else (src.get! i).toNat % 16) else ob
termination_by (src.size - i) * 4096 + rem
decreasing_by all_goals (repeat' split) <;> omega
def g10_4096 (xs : ByteArray) : Array UInt64 := f10_4096 (Array.replicate (64 + 0 * xs.size) 0) xs 0 0 0
set_option maxHeartbeats 0 in
wp_compileS g10_4096 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i w rem : Nat) => ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ w + (src.size - i) * 4096 + rem ≤ 2 ^ 60 ∧ rem < 32
  measure fun (_ob : Array UInt64) (src : ByteArray) (i _w rem : Nat) => (src.size - i) * 4096 + rem
-- 10: big multiplier invariant
def f10_65536 (ob : Array UInt64) (src : ByteArray) (i w rem : Nat) : Array UInt64 :=
  if i < src.size then
    f10_65536 (ob.set! i (if 0 < rem then ob[i]! else UInt64.ofNat i)) src (if 0 < rem then i else i + 1) (w + 1)
      (if 0 < rem then rem - 1 else (src.get! i).toNat % 16) else ob
termination_by (src.size - i) * 65536 + rem
decreasing_by all_goals (repeat' split) <;> omega
def g10_65536 (xs : ByteArray) : Array UInt64 := f10_65536 (Array.replicate (64 + 0 * xs.size) 0) xs 0 0 0
set_option maxHeartbeats 0 in
wp_compileS g10_65536 max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i w rem : Nat) => ob.size = 64 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ w + (src.size - i) * 65536 + rem ≤ 2 ^ 60 ∧ rem < 32
  measure fun (_ob : Array UInt64) (src : ByteArray) (i _w rem : Nat) => (src.size - i) * 65536 + rem
end Nano.Mic
