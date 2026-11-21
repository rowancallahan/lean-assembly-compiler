import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.Impl1
/- TinySmall: the 3-op subset (LOAD, STORE, nop) of `tinyCompile`; small enough (12 slots) for the machine theorem. -/
namespace Proven.Frontx.TinySm
open Proven Proven.Frontx
def tc : List UInt8 → List UInt8
  | op :: a :: rest =>
    if op == 2 then 0x83 :: 0x42 :: 0x05 :: 0 :: tc rest
    else if op == 3 then 0x23 :: 0 :: 0x56 :: 0 :: tc rest
    else 0x13 :: 0 :: 0 :: 0 :: tc rest
  | _ => [0x67, 0x80, 0, 0]
frontx_view tc
frontx_compile tc.view from tc.view.eq measure fun B i => B.size - i
def tinySm (xs : ByteArray) : List UInt8 := tc xs.data.toList
theorem tinySm_eq (xs : ByteArray) : tinySm xs = tc.view xs 0 := rfl
frontx_entry tinySm from tinySm_eq
frontx_implements_list tinySm
#print axioms tinySm.implements1
end Proven.Frontx.TinySm
