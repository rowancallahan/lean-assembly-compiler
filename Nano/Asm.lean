/- nano assembler: records [op, a, b, c] (4 bytes each) -> RISC-V words.  Written in the front end's list style (see
   Riscv/Frontx/TinySelf.lean): one pass, no helper functions, byte arithmetic only; every macro has <= 7 clauses (the
   front end rejects longer `if` chains).  `op & 7` is the funct3 field.  I-type: rd=a rs1=b imm; R-type: rd=a rs1=b rs2=c.
     0 ADDI imm=sext8 c   1 SLLI shamt=c   3 LD imm=8c   4 LBU imm=c   5 SRLI shamt=c   6 ORI imm=c   8 ADDI imm=8c
     7 BGEU rs1=b rs2=c (a = 0), branch offset +12 (skips the next two records)
     11 SD rs2=a rs1=b imm=8c      16 SB rs2=a rs1=b imm=c
     14 OR   24 ADD   32 SUB   40 MUL   (rd=a rs1=b rs2=c)        48 RET (a = 0, b = 1, c = 0: jalr x0, 0(ra))
   Any other op is not a nano record (the output is then unspecified). -/
namespace Nano

set_option hygiene false in
macro "X0" : term => `(if op == 3 || op == 4 then (((a &&& 1).toUInt64 <<< 7).toUInt8) ||| (3 : UInt8)
  else if op == 0 || op == 1 || op == 5 || op == 6 || op == 8 then (((a &&& 1).toUInt64 <<< 7).toUInt8) ||| (0x13 : UInt8)
  else if op == 11 then (0x23 : UInt8)
  else if op == 16 then (((c &&& 1).toUInt64 <<< 7).toUInt8) ||| (0x23 : UInt8)
  else if op == 14 || op == 24 || op == 32 || op == 40 then (((a &&& 1).toUInt64 <<< 7).toUInt8) ||| (0x33 : UInt8)
  else if op == 7 then (0x63 : UInt8)
  else if op == 48 then (((a &&& 1).toUInt64 <<< 7).toUInt8) ||| (0x67 : UInt8)
  else (0x13 : UInt8))
set_option hygiene false in
macro "X1" : term => `(if op == 11 then ((c &&& 3).toUInt64 <<< 2).toUInt8 ||| (0x30 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 16 then (((c >>> 1) &&& (15 : UInt8))) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 7 then (0x76 : UInt8) ||| (((b &&& 1).toUInt64 <<< 7).toUInt8)
  else (a >>> 1) ||| ((op &&& 7).toUInt64 <<< 4).toUInt8 ||| (((b &&& 1).toUInt64 <<< 7).toUInt8))
set_option hygiene false in
macro "X2" : term => `(if op == 3 || op == 8 then (b >>> 1) ||| (((c &&& 1).toUInt64 <<< 7).toUInt8)
  else if op == 11 || op == 16 then (b >>> 1) ||| ((a &&& 15).toUInt64 <<< 4).toUInt8
  else (b >>> 1) ||| ((c &&& 15).toUInt64 <<< 4).toUInt8)
set_option hygiene false in
macro "X3" : term => `(if op == 3 || op == 8 then c >>> 1
  else if op == 0 then (c >>> 4) ||| (if c < 128 then (0 : UInt8) else 0xF0)
  else if op == 11 then ((c >>> 2).toUInt64 <<< 1).toUInt8 ||| (a >>> 4)
  else if op == 16 then a >>> 4
  else if op == 32 then (c >>> 4) ||| (0x40 : UInt8)
  else if op == 40 then (c >>> 4) ||| (2 : UInt8)
  else c >>> 4)

def asm : List UInt8 → List UInt8
  | op :: a :: b :: c :: rest => X0 :: X1 :: X2 :: X3 :: asm rest
  | _ => []

end Nano
