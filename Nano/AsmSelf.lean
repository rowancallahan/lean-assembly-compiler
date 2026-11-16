import Nano.Asm
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Riscv.Frontx.Checked
/- the assembler stage compiled by OUR compiler (front end `frontx_compile`, list view), with a machine theorem -/
namespace Nano.Self
open Proven Proven.Frontx

frontx_view Nano.asm
set_option maxHeartbeats 0 in
frontx_compile Nano.asm.view from Nano.asm.view.eq measure fun B i => B.size - i

def nanoAsm (xs : ByteArray) : List UInt8 := Nano.asm xs.data.toList
theorem nanoAsm_eq (xs : ByteArray) : nanoAsm xs = Nano.asm.view xs 0 := rfl
frontx_entry nanoAsm from nanoAsm_eq
set_option maxHeartbeats 0 in
frontx_implements_listC nanoAsm
#print axioms nanoAsm.implements1

end Nano.Self
