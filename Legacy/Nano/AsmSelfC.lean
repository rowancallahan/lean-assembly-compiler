/- The assembler stage compiled by OUR compiler (front end `frontx_compile`, list view), part 1: the view and the
compile; its machine theorem in Nano/AsmSelf.lean (split in two files to keep each build ≤ 5 min). -/
import Legacy.Nano.Asm
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.Impl1
import Legacy.Riscv.Frontx.Checked
namespace Nano.Self
open Proven Proven.Frontx

frontx_view Nano.asm
set_option maxHeartbeats 0 in
frontx_compile Nano.asm.view from Nano.asm.view.eq measure fun B i => B.size - i

end Nano.Self
