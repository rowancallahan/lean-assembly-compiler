import Legacy.Nano.ElabBSplit
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.Impl1
import Legacy.Nano.CheckedSpill
/- stage 1a of the split lexer (`Nano.B.vB`, the validator, Nano/ElabBSplit.lean) compiled by OUR compiler (front end
`frontx_compile`, list view), with a machine theorem `Nano.Self.vBE.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx

frontx_view Nano.B.lv
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile Nano.B.lv.view from Nano.B.lv.view.eq measure fun B i k m _ _ _ _ _ _ _ =>
  (if m == 5 then 2 * (B.size - k) + 3 else if m == 0 then B.size - k + 1 else 0) + (B.size - i)

def vBE (xs : ByteArray) : List UInt8 := Nano.B.vB xs.data.toList
theorem vBE_eq (xs : ByteArray) : vBE xs = Nano.B.lv.view xs 0 0 5 0 0 0 0 0 0 0 := rfl
frontx_entry vBE from vBE_eq
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_implements_listCS vBE
#print axioms vBE.implements1

end Nano.Self
