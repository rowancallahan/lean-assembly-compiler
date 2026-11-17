import Nano.AsmSelfC
/- the assembler stage compiled by OUR compiler (front end `frontx_compile`, list view; Nano/AsmSelfC.lean), with a
machine theorem -/
namespace Nano.Self
open Proven Proven.Frontx

def nanoAsm (xs : ByteArray) : List UInt8 := Nano.asm xs.data.toList
theorem nanoAsm_eq (xs : ByteArray) : nanoAsm xs = Nano.asm.view xs 0 := rfl
frontx_entry nanoAsm from nanoAsm_eq
set_option maxHeartbeats 0 in
frontx_implements_listC nanoAsm
#print axioms nanoAsm.implements1

end Nano.Self
