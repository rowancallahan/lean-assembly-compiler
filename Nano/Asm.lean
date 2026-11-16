/- nano assembler: records [op, a, b, c] (4 bytes each) -> RISC-V words.  Written in the front end's list style (see
   Riscv/Frontx/TinySelf.lean): one pass, no helper functions, byte arithmetic only.
     0 LD rd=a rs1=b, offset 8c      1 SD rs2=a rs1=b, offset 8c      2 ADDI rd=a rs1=b, imm = 8 * sext8 c
     3 ORI rd=a rs1=b imm=c          4 SLLI rd=a rs1=b shamt=c        5 ADD / 6 SUB / 7 MUL rd=a rs1=b rs2=c
     8 RET                           (anything else: nop)
     9 LBU rd=a rs1=b off=c          10 SB rs2=a rs1=b off=c          11 SRLI rd=a rs1=b shamt=c      12 OR rd=a rs1=b rs2=c
     13 BGEU rs1=a rs2=b, offset +12 (skips the next two records)     14 ADDI rd=a rs1=b imm=sext8 c (unscaled)   -/
namespace Nano

set_option hygiene false in
macro "X0" : term => `(if op == 0 || op == 9 then (((a &&& 1).toUInt64 <<< 7).toUInt8) ||| (3 : UInt8)
  else if op == 1 then (0x23 : UInt8)
  else if op == 10 then (((c &&& 1).toUInt64 <<< 7).toUInt8) ||| (0x23 : UInt8)
  else if op == 2 || op == 3 || op == 4 || op == 11 || op == 14 then (((a &&& 1).toUInt64 <<< 7).toUInt8) ||| (0x13 : UInt8)
  else if op == 5 || op == 6 || op == 7 || op == 12 then (((a &&& 1).toUInt64 <<< 7).toUInt8) ||| (0x33 : UInt8)
  else if op == 13 then (0x63 : UInt8)
  else if op == 8 then 0x67 else 0x13)
set_option hygiene false in
macro "X1" : term => `(if op == 0 then (a >>> 1) ||| (0x30 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 9 then (a >>> 1) ||| (0x40 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 1 then ((c &&& 3).toUInt64 <<< 2).toUInt8 ||| (0x30 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 10 then (((c >>> 1) &&& (15 : UInt8))) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 2 || op == 14 then (a >>> 1) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 3 then (a >>> 1) ||| (0x60 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 4 then (a >>> 1) ||| (0x10 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 11 then (a >>> 1) ||| (0x50 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 5 || op == 6 || op == 7 then (a >>> 1) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 12 then (a >>> 1) ||| (0x60 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 13 then (0x76 : UInt8) ||| (((a &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 8 then (0x80 : UInt8) else 0)
set_option hygiene false in
macro "X2" : term => `(if op == 0 || op == 2 then (b >>> 1) ||| (((c &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 1 || op == 10 then (b >>> 1) ||| ((a &&& 15).toUInt64 <<< 4).toUInt8
  else if op == 13 then (a >>> 1) ||| ((b &&& 15).toUInt64 <<< 4).toUInt8
  else if op == 3 || op == 4 || op == 5 || op == 6 || op == 7 || op == 9 || op == 11 || op == 12 || op == 14 then
    (b >>> 1) ||| ((c &&& 15).toUInt64 <<< 4).toUInt8
  else (0 : UInt8))
set_option hygiene false in
macro "X3" : term => `(if op == 0 then c >>> 1
  else if op == 1 then ((c >>> 2).toUInt64 <<< 1).toUInt8 ||| (a >>> 4)
  else if op == 2 then ((c &&& 127) >>> 1) ||| (if c < 128 then (0 : UInt8) else 0xC0)
  else if op == 3 || op == 4 || op == 9 || op == 11 || op == 12 then c >>> 4
  else if op == 10 then a >>> 4
  else if op == 13 then b >>> 4
  else if op == 14 then (c >>> 4) ||| (if c < 128 then (0 : UInt8) else 0xF0)
  else if op == 5 || op == 7 then (c >>> 4) ||| (if op == 5 then (0 : UInt8) else 2)
  else if op == 6 then (c >>> 4) ||| (0x40 : UInt8) else 0)

def asm : List UInt8 → List UInt8
  | op :: a :: b :: c :: rest => X0 :: X1 :: X2 :: X3 :: asm rest
  | _ => []

end Nano
