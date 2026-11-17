import Nano.ExpandM
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Riscv.Frontx.Checked
/- the micro-op expander `mexp` as the record-per-step machine `Nano.MX.mx` (Nano/ExpandM.lean), compiled by OUR
compiler (front end `frontx_compile`, list view), with a machine theorem `Nano.Self.nanoExpM.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx

frontx_view Nano.MX.mx
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile Nano.MX.mx.view from Nano.MX.mx.view.eq measure
  fun B i k ph _ => (B.size - i) * 32 + (if ph = 0 then 1 else 0) + 2 * (15 - k.toNat)

def nanoExpM (xs : ByteArray) : List UInt8 := Nano.MX.mx xs.data.toList 0 0 0
theorem nanoExpM_eq (xs : ByteArray) : nanoExpM xs = Nano.MX.mx.view xs 0 0 0 0 := rfl
frontx_entry nanoExpM from nanoExpM_eq
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_implements_listC nanoExpM
#print axioms nanoExpM.implements1

end Nano.Self
