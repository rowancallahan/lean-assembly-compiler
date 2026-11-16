import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Riscv.Frontx.Checked
namespace P4
open Proven Proven.Frontx

set_option hygiene false in
macro "X0" : term => `(if op == 0 || op == 9 then (((a &&& 1).toUInt64 <<< 7).toUInt8) ||| (3 : UInt8)
  else if op == 1 then (0x23 : UInt8)
  else if op == 2 || op == 3 || op == 4 || op == 14 then (((a &&& 1).toUInt64 <<< 7).toUInt8) ||| (0x13 : UInt8)
  else if op == 5 || op == 6 || op == 7 then (((a &&& 1).toUInt64 <<< 7).toUInt8) ||| (0x33 : UInt8)
  else if op == 8 then (0x67 : UInt8)
  else (0x13 : UInt8))
set_option hygiene false in
macro "X1" : term => `(if op == 0 then (a >>> 1) ||| (0x30 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 9 then (a >>> 1) ||| (0x40 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 1 then ((c &&& 3).toUInt64 <<< 2).toUInt8 ||| (0x30 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 2 || op == 14 then (a >>> 1) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 3 then (a >>> 1) ||| (0x60 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 4 then (a >>> 1) ||| (0x10 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 5 || op == 6 || op == 7 then (a >>> 1) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 8 then (0x80 : UInt8)
  else (0 : UInt8))
set_option hygiene false in
macro "X2" : term => `(if op == 0 || op == 2 then (b >>> 1) ||| (((c &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 1 then (b >>> 1) ||| ((a &&& 15).toUInt64 <<< 4).toUInt8
  else if op == 3 || op == 4 || op == 5 || op == 6 || op == 7 || op == 9 || op == 14 then (b >>> 1) ||| ((c &&& 15).toUInt64 <<< 4).toUInt8
  else (0 : UInt8))
set_option hygiene false in
macro "X3" : term => `(if op == 0 then c >>> 1
  else if op == 1 then ((c >>> 2).toUInt64 <<< 1).toUInt8 ||| (a >>> 4)
  else if op == 2 then ((c &&& 127) >>> 1) ||| (if c < 128 then (0 : UInt8) else 0xC0)
  else if op == 3 || op == 4 || op == 9 then c >>> 4
  else if op == 14 then (c >>> 4) ||| (if c < 128 then (0 : UInt8) else 0xF0)
  else if op == 5 || op == 7 then (c >>> 4) ||| (if op == 5 then (0 : UInt8) else 2)
  else if op == 6 then (c >>> 4) ||| (0x40 : UInt8)
  else (0 : UInt8))

def asm : List UInt8 → List UInt8
  | op :: a :: b :: c :: rest => X0 :: X1 :: X2 :: X3 :: asm rest
  | _ => []
frontx_view P4.asm
set_option maxHeartbeats 0 in
frontx_compile P4.asm.view from P4.asm.view.eq measure fun B i => B.size - i
end P4
