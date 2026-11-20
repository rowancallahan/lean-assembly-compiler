import Nano.InlRP
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.Impl1
import Legacy.Nano.CheckedSpill
namespace Nano.IR
def wwU (xs : List UInt8) (ph k : Nat) : List UInt8 :=
  match xs with
  | [] =>
    if ph == 2 then 7 :: 0 :: []
    else if ph == 0 then 0 :: 0 :: 7 :: []
    else if k == 0 then wwU [] 2 k
    else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 :: wwU [] 1 0
  | b :: t =>
    if ph == 2 then b :: wwU t 2 k
    else if ph == 0 then 0 :: 0 :: wwU t 1 b.toNat
    else if k == 0 then wwU (b :: t) 2 k
    else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 ::
      wwU (b :: t) 1 0
termination_by 4 * xs.length + 2 * (if ph == 2 then 0 else if ph == 0 then 2 else 1) + (if k == 0 then 0 else 1)
decreasing_by
  all_goals
    simp_all (config := {decide := true}) only [List.length_cons, List.length_nil, beq_iff_eq, if_true, if_false]
    all_goals first
      | omega
      | (have := UInt8.toNat_lt_size ‹UInt8›; simp only [UInt8.size] at *; (repeat' split) <;> omega)
      | ((repeat' split) <;> omega)
end Nano.IR
/- the inliner's last stage `W` (`Nano.IR.wwU`, Nano/InlRP.lean) compiled by OUR compiler (front end `frontx_compile`,
list view, hand-written view equation: the machine has non-consuming calls), with a machine theorem
`Nano.Self.inlWU.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx

def wwvU (B : ByteArray) (i ph k : Nat) : List UInt8 := Nano.IR.wwU (view B i) ph k

theorem wwvU_eq (B : ByteArray) (i ph k : Nat) : wwvU B i ph k =
    if h : i < B.size then
      if ph == 2 then B[i] :: wwvU B (i + 1) 2 k
      else if ph == 0 then 0 :: 0 :: wwvU B (i + 1) 1 B[i].toNat
      else if k == 0 then wwvU B i 2 k
      else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 ::
        wwvU B i 1 0
    else
      if ph == 2 then 7 :: 0 :: []
      else if ph == 0 then 0 :: 0 :: 7 :: []
      else if k == 0 then wwvU B i 2 k
      else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 ::
        wwvU B i 1 0 := by
  unfold wwv
  by_cases h : i < B.size
  · rw [dif_pos h, view_eq B i, dif_pos h, Nano.IR.wwU]
  · rw [dif_neg h, view_eq B i, dif_neg h, Nano.IR.wwU]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile wwvU from wwvU_eq measure
  fun B i ph k => 4 * (B.size - i) + 2 * (if ph == 2 then 0 else if ph == 0 then 2 else 1) + (if k == 0 then 0 else 1)

def inlWU (xs : ByteArray) : List UInt8 := Nano.IR.wwU xs.data.toList 0 0
theorem inlWU_eq (xs : ByteArray) : inlWU xs = wwvU xs 0 0 0 := rfl
frontx_entry inlWU from inlWU_eq
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in

end Nano.Self
