import Nano.InlRP
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.Impl1
import Legacy.Nano.CheckedSpill
namespace Nano.IR
def wwT (xs : List UInt8) (ph k : Nat) : List UInt8 :=
  match xs with
  | [] =>
    if ph == 2 then 7 :: 0 :: []
    else if ph == 0 then 0 :: 0 :: 7 :: []
    else if k == 0 then wwT [] 2 k
    else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 :: wwT [] 1 (k - 1)
  | b :: t =>
    if ph == 2 then b :: wwT t 2 k
    else if ph == 0 then 0 :: 0 :: wwT t 1 b.toNat
    else if k == 0 then wwT (b :: t) 2 k
    else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 ::
      wwT (b :: t) 1 (k - 1)
termination_by 1024 * xs.length + 512 * (if ph == 2 then 0 else if ph == 0 then 2 else 1) + k
decreasing_by
  all_goals
    simp_all (config := {decide := true}) only [List.length_cons, List.length_nil, beq_iff_eq, if_true, if_false]
    all_goals first
      | omega
      | (have := UInt8.toNat_lt_size ‹UInt8›; simp only [UInt8.size] at *; (repeat' split) <;> omega)
      | ((repeat' split) <;> omega)
end Nano.IR
/- the inliner's last stage `W` (`Nano.IR.wwT`, Nano/InlRP.lean) compiled by OUR compiler (front end `frontx_compile`,
list view, hand-written view equation: the machine has non-consuming calls), with a machine theorem
`Nano.Self.inlWT.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx

def wwvT (B : ByteArray) (i ph k : Nat) : List UInt8 := Nano.IR.wwT (view B i) ph k

theorem wwvT_eq (B : ByteArray) (i ph k : Nat) : wwvT B i ph k =
    if h : i < B.size then
      if ph == 2 then B[i] :: wwvT B (i + 1) 2 k
      else if ph == 0 then 0 :: 0 :: wwvT B (i + 1) 1 B[i].toNat
      else if k == 0 then wwvT B i 2 k
      else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 ::
        wwvT B i 1 (k - 1)
    else
      if ph == 2 then 7 :: 0 :: []
      else if ph == 0 then 0 :: 0 :: 7 :: []
      else if k == 0 then wwvT B i 2 k
      else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 ::
        wwvT B i 1 (k - 1) := by
  unfold wwv
  by_cases h : i < B.size
  · rw [dif_pos h, view_eq B i, dif_pos h, Nano.IR.wwT]
  · rw [dif_neg h, view_eq B i, dif_neg h, Nano.IR.wwT]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile wwvT from wwvT_eq measure
  fun B i ph k => 1024 * (B.size - i) + 512 * (if ph == 2 then 0 else if ph == 0 then 2 else 1) + k

def inlWT (xs : ByteArray) : List UInt8 := Nano.IR.wwT xs.data.toList 0 0
theorem inlWT_eq (xs : ByteArray) : inlWT xs = wwvT xs 0 0 0 := rfl
frontx_entry inlWT from inlWT_eq
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in

end Nano.Self
