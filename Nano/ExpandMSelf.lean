import Nano.ExpandM
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Nano.CheckedSpill
/- the micro-op expander `mexp` as the record-per-step machine `Nano.MX.mx` (Nano/ExpandM.lean), compiled by OUR
compiler (front end `frontx_compile`, list view), with a machine theorem `Nano.Self.nanoExpM.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx Nano.MX

/-- the machine on the input block from index `i` on (written by hand: `frontx_view`'s generic equation prover
loops on the non-consuming recursive calls) -/
def mxv (B : ByteArray) (i k ph : Nat) (c : UInt64) : List UInt8 := Nano.MX.mx (view B i) k ph c

theorem mxv_eq (B : ByteArray) (i k ph : Nat) (c : UInt64) : mxv B i k ph c =
    if h : i < B.size then
      if h2 : i + 1 < B.size then
        if ph = 0 then
          (if B[i] < 6 then (if B[i] == 0 then (if k == 0 then mxv B i k 1 (0x3021F05 : UInt64) else if k == 1 then mxv B i k 1 (0x31F1F01 : UInt64) else mxv B i k 1 (0x4000A1C00 : UInt64)) else if B[i] == 1 then (mxv B i k 1 (0x4071C0504 : UInt64)) else if B[i] == 2 then (if k == 0 then mxv B i k 1 (0x8050501 : UInt64) else if k == 1 then mxv B i k 1 (0x1001C0604 : UInt64) else mxv B i k 1 (0x40605050E : UInt64)) else if B[i] == 3 then (if k == 0 then mxv B i k 1 (0xF81F1F00 : UInt64) else if k == 1 then mxv B i k 1 (0xC1F0007 : UInt64) else if k == 2 then mxv B i k 1 (0xFF000A00 : UInt64) else if k == 3 then mxv B i k 1 (0x10030 : UInt64) else mxv B i k 1 (0x4001F050B : UInt64)) else if B[i] == 4 then (mxv B i k 1 (0x4011C1C08 : UInt64)) else (mxv B i k 1 (0x400000500 : UInt64))) else if B[i] < 12 then (if B[i] == 6 then (if k == 0 then mxv B i k 1 (0x8050501 : UInt64) else mxv B i k 1 (0x500050506 : UInt64)) else if B[i] == 7 then (mxv B i k 1 (0x5001F0503 : UInt64)) else if B[i] == 8 then (if k == 0 then mxv B i k 1 (0x1F0603 : UInt64) else if k == 1 then mxv B i k 1 (0x11F0503 : UInt64) else if k == 2 then mxv B i k 1 (0x11F1F08 : UInt64) else if k == 3 then mxv B i k 1 (0x206050500 : UInt64) else mxv B i k 1 (0x4001F050B : UInt64)) else if B[i] == 9 then (if k == 0 then mxv B i k 1 (0x1F0503 : UInt64) else if k == 1 then mxv B i k 1 (0x1001F1F08 : UInt64) else mxv B i k 1 (0x4001F050B : UInt64)) else if B[i] == 10 then (mxv B i k 1 (0x500050605 : UInt64)) else (mxv B i k 1 (0x5000D0610 : UInt64))) else (mxv B i k 1 (0x400010030 : UInt64)))
        else if 6 ≤ k then
          (if (c >>> 33) &&& 1 == 1 then B[i + 1] else c.toUInt8) :: (c >>> 8).toUInt8 :: (c >>> 16).toUInt8 ::
        (if (c >>> 32) &&& 1 == 1 then B[i + 1] else (c >>> 24).toUInt8) :: mxv B (i + 2) 0 0 0
        else if (c >>> 34) &&& 1 == 1 then
          (if (c >>> 33) &&& 1 == 1 then B[i + 1] else c.toUInt8) :: (c >>> 8).toUInt8 :: (c >>> 16).toUInt8 ::
        (if (c >>> 32) &&& 1 == 1 then B[i + 1] else (c >>> 24).toUInt8) :: mxv B (i + 2) 0 0 0
        else
          (if (c >>> 33) &&& 1 == 1 then B[i + 1] else c.toUInt8) :: (c >>> 8).toUInt8 :: (c >>> 16).toUInt8 ::
        (if (c >>> 32) &&& 1 == 1 then B[i + 1] else (c >>> 24).toUInt8) :: mxv B i (k + 1) 0 0
      else []
    else [] := by
  unfold mxv
  by_cases h : i < B.size
  · rw [dif_pos h]
    by_cases h2 : i + 1 < B.size
    · rw [dif_pos h2, view_eq B i, dif_pos h, view_eq B (i + 1), dif_pos h2, Nano.MX.mx_c]
    · rw [dif_neg h2, view_eq B i, dif_pos h, view_eq B (i + 1), dif_neg h2, Nano.MX.mx]; simp
  · rw [dif_neg h, view_eq B i, dif_neg h, Nano.MX.mx]; simp

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile mxv from mxv_eq measure
  fun B i k ph _ => (B.size - i) * 32 + 2 * (15 - k) + (1 - ph)

def nanoExpM (xs : ByteArray) : List UInt8 := Nano.MX.mx xs.data.toList 0 0 0
theorem nanoExpM_eq (xs : ByteArray) : nanoExpM xs = mxv xs 0 0 0 0 := rfl
frontx_entry nanoExpM from nanoExpM_eq
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_implements_listCS nanoExpM
#print axioms nanoExpM.implements1

end Nano.Self
