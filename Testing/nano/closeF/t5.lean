import Nano.InlRP
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.Impl1
import Legacy.Nano.CheckedSpill
namespace Nano.Self
open Proven Proven.Frontx
def t5 (xs : List UInt8) (ph k : Nat) : List UInt8 :=
  match xs with
  | [] => if k == 0 then [] else 1 :: t5 [] 1 (k - 1)
  | b :: t => b :: t5 t ph k
termination_by 1024 * xs.length + k
decreasing_by all_goals (simp_all; try omega)
def t5v (B : ByteArray) (i ph k : Nat) : List UInt8 := t5 (view B i) ph k
theorem t5v_eq (B : ByteArray) (i ph k : Nat) : t5v B i ph k =
    if h : i < B.size then B[i] :: t5v B (i + 1) ph k else (if k == 0 then [] else 1 :: t5v B i 1 (k - 1)) := by
  unfold t5v; by_cases h : i < B.size
  · rw [dif_pos h, view_eq B i, dif_pos h, t5]
  · rw [dif_neg h, view_eq B i, dif_neg h, t5]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile t5v from t5v_eq measure fun B i _ k => 1024 * (B.size - i) + k
end Nano.Self
