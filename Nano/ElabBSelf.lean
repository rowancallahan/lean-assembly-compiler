import Nano.ElabB
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Riscv.Frontx.Checked
/- stage 1 of nanoElabB (`Nano.B.lexB`) compiled by OUR compiler (front end `frontx_compile`, list view) -/
namespace Nano.Self
open Proven Proven.Frontx

frontx_view Nano.B.lx
set_option maxHeartbeats 0 in
frontx_compile Nano.B.lx.view from Nano.B.lx.view.eq measure fun B i k m _ _ _ _ _ _ => (if m = 0 then B.size + 1 else 0) + (B.size - i)
