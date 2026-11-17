import Nano.InlRP
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Nano.CheckedSpill
namespace Nano.Self
open Proven Proven.Frontx
def t1 (xs : List UInt8) (ph k : Nat) : List UInt8 :=
  match xs with
  | [] => []
  | b :: t => if ph == 0 then 0 :: t1 t 1 b.toNat else b :: t1 t ph k
def t1v (B : ByteArray) (i ph k : Nat) : List UInt8 := t1 (view B i) ph k
theorem t1v_eq (B : ByteArray) (i ph k : Nat) : t1v B i ph k =
    if h : i < B.size then (if ph == 0 then 0 :: t1v B (i + 1) 1 B[i].toNat else B[i] :: t1v B (i + 1) ph k) else [] := by
  unfold t1v; by_cases h : i < B.size
  · rw [dif_pos h, view_eq B i, dif_pos h, t1]
  · rw [dif_neg h, view_eq B i, dif_neg h, t1]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile t1v from t1v_eq measure fun B i _ _ => B.size - i
end Nano.Self
