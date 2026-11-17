import Nano.InlRP
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Nano.CheckedSpill
namespace Nano.Self
open Proven Proven.Frontx
def t6 (xs : List UInt8) (ph k : Nat) : List UInt8 :=
  match xs with
  | [] => if k == 0 then [] else UInt8.ofNat (8 * k) :: t6 [] 1 (k - 1)
  | b :: t => b :: t6 t ph k
termination_by 1024 * xs.length + k
decreasing_by all_goals (simp_all; try omega)
def t6v (B : ByteArray) (i ph k : Nat) : List UInt8 := t6 (view B i) ph k
theorem t6v_eq (B : ByteArray) (i ph k : Nat) : t6v B i ph k =
    if h : i < B.size then B[i] :: t6v B (i + 1) ph k else (if k == 0 then [] else UInt8.ofNat (8 * k) :: t6v B i 1 (k - 1)) := by
  unfold t6v; by_cases h : i < B.size
  · rw [dif_pos h, view_eq B i, dif_pos h, t6]
  · rw [dif_neg h, view_eq B i, dif_neg h, t6]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile t6v from t6v_eq measure fun B i _ k => 1024 * (B.size - i) + k
end Nano.Self
