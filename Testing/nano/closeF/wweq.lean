import Nano.InlRP
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Nano.CheckedSpill
/- the inliner's last stage `W` (`Nano.IR.ww`, Nano/InlRP.lean) compiled by OUR compiler (front end `frontx_compile`,
list view, hand-written view equation: the machine has non-consuming calls), with a machine theorem
`Nano.Self.inlW.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx

def wwv (B : ByteArray) (i ph k : Nat) : List UInt8 := Nano.IR.ww (view B i) ph k

theorem wwv_eq (B : ByteArray) (i ph k : Nat) : wwv B i ph k =
    if h : i < B.size then
      if ph == 2 then B[i] :: wwv B (i + 1) 2 k
      else if ph == 0 then 0 :: 0 :: wwv B (i + 1) 1 B[i].toNat
      else if k == 0 then wwv B i 2 k
      else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 ::
        wwv B i 1 (k - 1)
    else
      if ph == 2 then 7 :: 0 :: 10 :: 0 :: 11 :: 0 :: 10 :: 8 :: 11 :: 1 :: 10 :: 16 :: 11 :: 2 :: 10 :: 24 :: 11 :: 3 ::
        10 :: 32 :: 11 :: 4 :: 10 :: 40 :: 11 :: 5 :: 10 :: 48 :: 11 :: 6 :: 10 :: 56 :: 11 :: 7 :: 12 :: 0 :: []
      else if ph == 0 then 0 :: 0 :: 7 :: 0 :: 10 :: 0 :: 11 :: 0 :: 10 :: 8 :: 11 :: 1 :: 10 :: 16 :: 11 :: 2 :: 10 :: 24 ::
        11 :: 3 :: 10 :: 32 :: 11 :: 4 :: 10 :: 40 :: 11 :: 5 :: 10 :: 48 :: 11 :: 6 :: 10 :: 56 :: 11 :: 7 :: 12 :: 0 :: []
      else if k == 0 then wwv B i 2 k
      else 1 :: 0 :: 2 :: 6 :: 2 :: 5 :: 2 :: 4 :: 2 :: 3 :: 2 :: 2 :: 2 :: 1 :: 2 :: 0 :: 3 :: 0 :: 4 :: 0 ::
        wwv B i 1 (k - 1) := by
  unfold wwv
  by_cases h : i < B.size
  · rw [dif_pos h, view_eq B i, dif_pos h, Nano.IR.ww]
  · rw [dif_neg h, view_eq B i, dif_neg h, Nano.IR.ww]

end Nano.Self
