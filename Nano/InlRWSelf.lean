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
    if ph < 1 then
      if h : i < B.size then (if 256 ≤ B[i].toNat then [] else 0 :: 0 :: wwv B (i + 1) 1 B[i].toNat 0)
      else 0 :: 0 :: wwv B i 3 0 0
    else if ph < 2 then
      if k < 1 then wwv B i 2 0 0
      else if q < 4 then
        (if q == 0 then 1 else 2) :: (if q == 0 then 0 else if q == 1 then 5 else if q == 2 then 3 else 1) :: 2 ::
          (if q == 0 then 6 else if q == 1 then 4 else if q == 2 then 2 else 0) :: wwv B i 1 k (q + 1)
      else 3 :: 0 :: 4 :: 0 :: wwv B i 1 (k - 1) 0
    else if ph < 3 then
      if h : i < B.size then B[i] :: wwv B (i + 1) 2 0 0 else wwv B i 3 0 0
    else
      if q < 8 then
        (if q == 0 then 7 else 11) ::
          (if q < 4 then (if q == 0 then 0 else if q == 1 then 0 else if q == 2 then 1 else 2)
           else (if q == 4 then 3 else if q == 5 then 4 else if q == 6 then 5 else 6)) :: 10 ::
          (if q < 4 then (if q == 0 then 0 else if q == 1 then 8 else if q == 2 then 16 else 24)
           else (if q == 4 then 32 else if q == 5 then 40 else if q == 6 then 48 else 56)) :: wwv B i 3 0 (q + 1)
      else 11 :: 7 :: 12 :: 0 :: [] := by
  unfold wwv
  rw [Nano.IR.ww.eq_def]
  by_cases h0 : ph < 1
  · simp only [h0, if_true]
    by_cases h : i < B.size
    · rw [dif_pos h, view_eq B i, dif_pos h]
    · rw [dif_neg h, view_eq B i, dif_neg h]
  by_cases h1 : ph < 2
  · simp only [h0, h1, if_true, if_false]
  by_cases h2 : ph < 3
  · simp only [h0, h1, h2, if_true, if_false]
    by_cases h : i < B.size
    · rw [dif_pos h, view_eq B i, dif_pos h]
    · rw [dif_neg h, view_eq B i, dif_neg h]
  simp only [h0, h1, h2, if_false]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile wwv from wwv_eq measure fun B i ph k q => 4096 * (B.size - i) + 1024 * (3 - ph) + 10 * k + (9 - q)

def inlW (xs : ByteArray) : List UInt8 := Nano.IR.ww xs.data.toList 0 0 0
theorem inlW_eq (xs : ByteArray) : inlW xs = wwv xs 0 0 0 0 := rfl
frontx_entry inlW from inlW_eq
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_implements_listCS inlW
#print axioms inlW.implements1

end Nano.Self
