import Nano.ElabB
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Riscv.Frontx.Checked
/- stage 1 of nanoElabB (`Nano.B.lexB`, the lexer) compiled by OUR compiler (front end `frontx_compile`, list view),
with a machine theorem `Nano.Self.lexBE.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx

frontx_view Nano.B.lx
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile Nano.B.lx.view from Nano.B.lx.view.eq measure fun B i k m _ _ _ _ _ _ _ => (if m = 5 then 2 * B.size + 3 else if m = 0 then B.size + 1 else 0) + (B.size - i)

def lexBE (xs : ByteArray) : List UInt8 := Nano.B.lexB xs.data.toList
theorem lexBE_eq (xs : ByteArray) : lexBE xs = Nano.B.lx.view xs 0 0 5 0 0 0 0 0 0 0 := rfl
frontx_entry lexBE from lexBE_eq
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_implements_listC lexBE
#print axioms lexBE.implements1

end Nano.Self
