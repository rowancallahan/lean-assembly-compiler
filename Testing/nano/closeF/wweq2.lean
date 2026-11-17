import Nano.InlRP
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Nano.CheckedSpill
/- the inliner's last stage `W` (`Nano.IR.ww`, Nano/InlRP.lean) compiled by OUR compiler (front end `frontx_compile`,
list view, hand-written view equation: the machine has non-consuming calls), with a machine theorem
`Nano.Self.inlW.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx

def wwv (B : ByteArray) (i ph k q : Nat) : List UInt8 := Nano.IR.ww (view B i) ph k q

theorem wwv_eq (B : ByteArray) (i ph k q : Nat) : wwv B i ph k q =
    if ph == 1 then
      if k == 0 then wwv B i 2 0 0
      else (if q == 0 then 1 else if q == 4 then 3 else 2) ::
        (if q == 0 then 0 else if q == 1 then 5 else if q == 2 then 3 else if q == 3 then 1 else 0) ::
        (if q == 4 then 4 else 2) ::
        (if q == 0 then 6 else if q == 1 then 4 else if q == 2 then 2 else 0) ::
        (if q < 4 then wwv B i 1 k (q + 1) else wwv B i 1 (k - 1) 0)
    else if ph == 3 then
      (if q == 0 then 7 else 11) ::
        (if q < 4 then (if q == 0 then 0 else if q == 1 then 0 else if q == 2 then 1 else 2)
         else (if q == 4 then 3 else if q == 5 then 4 else if q == 6 then 5 else if q == 7 then 6 else 7)) ::
        (if q < 8 then 10 else 12) ::
        (if q < 4 then (if q == 0 then 0 else if q == 1 then 8 else if q == 2 then 16 else 24)
         else (if q == 4 then 32 else if q == 5 then 40 else if q == 6 then 48 else if q == 7 then 56 else 0)) ::
        (if q < 8 then wwv B i 3 0 (q + 1) else [])
    else if h : i < B.size then
      (if ph == 0 then 0 :: 0 :: wwv B (i + 1) 1 B[i].toNat 0 else B[i] :: wwv B (i + 1) 2 0 0)
    else (if ph == 0 then 0 :: 0 :: wwv B i 3 0 0 else wwv B i 3 0 0) := by
  unfold wwv
  rw [Nano.IR.ww.eq_def]
  by_cases h1 : ph = 1
  · subst h1; simp only [beq_self_eq_true, if_true]
  by_cases h3 : ph = 3
  · subst h3; simp only [show ((3 : Nat) == 1) = false from rfl, beq_self_eq_true, if_true, Bool.false_eq_true,
      if_false]
  simp only [beq_iff_eq, h1, h3, if_false]
  by_cases h : i < B.size
  · rw [dif_pos h, view_eq B i, dif_pos h]
  · rw [dif_neg h, view_eq B i, dif_neg h]

end Nano.Self
