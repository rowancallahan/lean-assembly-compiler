import Nano.InlRP
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.Impl1
import Legacy.Nano.CheckedSpill
/- the inliner's first stage `P` (`Nano.IR.pr`, Nano/InlRP.lean) compiled by OUR compiler (front end
`frontx_compile`, list view), with a machine theorem `Nano.Self.inlPR.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx

frontx_view Nano.IR.pr
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile Nano.IR.pr.view from Nano.IR.pr.view.eq measure fun B i _ _ => B.size - i

def inlPR (xs : ByteArray) : List UInt8 := Nano.IR.pr xs.data.toList 0 0
theorem inlPR_eq (xs : ByteArray) : inlPR xs = Nano.IR.pr.view xs 0 0 0 := rfl
frontx_entry inlPR from inlPR_eq
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_implements_listCS inlPR
#print axioms inlPR.implements1

end Nano.Self
