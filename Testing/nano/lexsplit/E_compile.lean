import Nano.ElabBSplitE
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Nano.CheckedSpill
/- stage 1b of the split lexer (`Nano.B.eB`, the emitter, Nano/ElabBSplit.lean) compiled by OUR compiler (front end
`frontx_compile`, list view), with a machine theorem `Nano.Self.eBE.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx

frontx_view Nano.B.le
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile Nano.B.le.view from Nano.B.le.view.eq measure fun B i k m _ _ _ _ _ _ _ =>
  (if m == 7 then B.size - i + 1 else 0) + (B.size - i)

end Nano.Self
