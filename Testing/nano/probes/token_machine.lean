import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Riscv.Frontx.Checked
namespace Q1
open Proven Proven.Frontx
/-- token machine with a depth scalar: tag, arg -> records (push: 5 records, binop: 5, letend: 3, ldv: 1) -/
def gf : UInt64 → List UInt8 → List UInt8
  | d, t :: a :: rest =>
    if t == 1 then
      0 :: 31 :: 31 :: 248 :: 7 :: 0 :: 31 :: 12 :: 0 :: 10 :: 0 :: 255 :: 48 :: 0 :: 1 :: 0 :: 11 :: 5 :: 31 :: 0 :: gf (d + 1) rest
    else if t == 2 then
      3 :: 6 :: 31 :: 0 :: 3 :: 5 :: 31 :: 1 :: 8 :: 31 :: 31 :: 1 :: a :: 5 :: 5 :: 6 :: 11 :: 5 :: 31 :: 0 :: gf (d - 1) rest
    else if t == 3 then
      3 :: 5 :: 31 :: 0 :: 8 :: 31 :: 31 :: a :: 11 :: 5 :: 31 :: 0 :: gf (d - a.toUInt64) rest
    else if t == 4 then
      3 :: 5 :: 31 :: (d - 1 - a.toUInt64).toUInt8 :: gf d rest
    else gf d rest
  | _, _ => []
frontx_view gf
set_option maxHeartbeats 0 in
frontx_compile gf.view from gf.view.eq measure fun d B i => B.size - i
end Q1
