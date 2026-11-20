import Nano.InlRP
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.Impl1
import Legacy.Nano.CheckedSpill
namespace Nano.Self
open Proven Proven.Frontx
def t2 (xs : List UInt8) (ph k : Nat) : List UInt8 :=
  match xs with
  | [] => if ph == 2 then [7] else t2 [] 2 k
  | b :: t => b :: t2 t ph k
termination_by 4 * xs.length + (if ph == 2 then 0 else 1)
decreasing_by all_goals (simp_all; try split <;> omega)
def t2v (B : ByteArray) (i ph k : Nat) : List UInt8 := t2 (view B i) ph k
theorem t2v_eq (B : ByteArray) (i ph k : Nat) : t2v B i ph k =
    if h : i < B.size then B[i] :: t2v B (i + 1) ph k else (if ph == 2 then [7] else t2v B i 2 k) := by
  unfold t2v; by_cases h : i < B.size
  · rw [dif_pos h, view_eq B i, dif_pos h, t2]
  · rw [dif_neg h, view_eq B i, dif_neg h, t2]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile t2v from t2v_eq measure fun B i ph _ => 4 * (B.size - i) + (if ph == 2 then 0 else 1)
end Nano.Self
