import Nano.InlRP
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.Impl1
import Legacy.Nano.CheckedSpill
namespace Nano.Self
open Proven Proven.Frontx
def t3 (xs : List UInt8) (ph k : Nat) : List UInt8 :=
  match xs with
  | [] => []
  | b :: t => b :: t3 t ph k
def t3v (B : ByteArray) (i ph k : Nat) : List UInt8 := t3 (view B i) ph k
theorem t3v_eq (B : ByteArray) (i ph k : Nat) : t3v B i ph k =
    if h : i < B.size then B[i] :: t3v B (i + 1) ph k else [] := by
  unfold t3v; by_cases h : i < B.size
  · rw [dif_pos h, view_eq B i, dif_pos h, t3]
  · rw [dif_neg h, view_eq B i, dif_neg h, t3]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile t3v from t3v_eq measure fun B i _ _ => B.size - i
end Nano.Self
