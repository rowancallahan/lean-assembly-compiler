import Nano.InlRP
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Nano.CheckedSpill
namespace Nano.Self
open Proven Proven.Frontx
def t4 (xs : List UInt8) (ph k : Nat) : List UInt8 :=
  match xs with
  | [] => []
  | b :: t => 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 :: t4 t ph k
def t4v (B : ByteArray) (i ph k : Nat) : List UInt8 := t4 (view B i) ph k
theorem t4v_eq (B : ByteArray) (i ph k : Nat) : t4v B i ph k =
    if h : i < B.size then 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 :: t4v B (i + 1) ph k else [] := by
  unfold t4v; by_cases h : i < B.size
  · rw [dif_pos h, view_eq B i, dif_pos h, t4]
  · rw [dif_neg h, view_eq B i, dif_neg h, t4]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile t4v from t4v_eq measure fun B i _ _ => B.size - i
end Nano.Self
