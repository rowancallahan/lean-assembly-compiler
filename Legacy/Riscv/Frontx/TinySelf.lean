/- TINYSELF: a minimal compiler `tinyCompile` (tiny language bytes → RISC-V bytes) written to be accepted by the
automatic front end (see Testing/notes/TINYSELF.md).  Tiny language: program = pairs (op, arg); registers: acc (t0),
i (t1); a0 = input, a1 = length, a2 = output pointer.  Every tiny instruction compiles to exactly 3 RISC-V words.
  0 ADDI k : acc += sext k      1 XORI k : acc ^= sext k    2 LOAD : acc = in[i]; i++
  3 STORE  : out[j++] = acc     4 JNZ k  : if acc ≠ 0 then pc += sext k    5 LEN : acc = n - i
  6 JZ k   : if acc = 0 then pc += sext k   (anything else: no-op `nop`)                                -/
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.Impl1
import Legacy.Riscv.Frontx.Checked

namespace Proven.Frontx.Tiny
open Proven Proven.Frontx

def sx (k : UInt8) : UInt64 := (k.toUInt64 ^^^ 128) - 128

set_option hygiene false in
macro "W0" : term => `(if op == 0 || op == 1 || op == 5 then (0x93 : UInt8) else if op == 2 then 0x83 else if op == 3 then 0x23
  else if op == 4 || op == 6 then (if a < 128 then 0 else 0x80) ||| 0x63 else if op == 7 || op == 8 then 0x13 else if op == 9 then 0x93 else 0x13)
set_option hygiene false in
macro "W1" : term => `(if op == 0 || op == 5 then (0x82 : UInt8) else if op == 1 then 0xC2 else if op == 2 then 0x42
  else if op == 4 then ((a &&& 7) + (a &&& 7)) ||| 0x90
  else if op == 6 then ((a &&& 7) + (a &&& 7)) ||| 0x80 else if op == 7 then 0x05 else if op == 8 then 0x06 else if op == 9 then 0x85 else 0)
set_option hygiene false in
macro "W2" : term => `(if op == 0 || op == 1 then ((a.toUInt64 <<< 4).toUInt8) ||| 2 else if op == 2 || op == 5 then (0x05 : UInt8) else if op == 3 then 0x56
  else if op == 4 || op == 6 then 0x02 else if op == 7 then 0x15 else if op == 8 then 0x16 else if op == 9 then 0xF5 else 0)
set_option hygiene false in
macro "W3" : term => `(if op == 0 || op == 1 then (a >>> 4) ||| (if a < 128 then 0 else 0xF0)
  else if op == 4 || op == 6 then ((a >>> 2) &&& (0x3E : UInt8)) ||| (if a < 128 then 0 else 0xC0) else if op == 9 then (0xFF : UInt8) else 0)

def tc : List UInt8 → List UInt8
  | op :: a :: rest => W0 :: W1 :: W2 :: W3 :: tc rest
  | _ => [0x67, 0x80, 0, 0]
frontx_view tc
set_option maxHeartbeats 0 in
frontx_compile tc.view from tc.view.eq measure fun B i => B.size - i

/-! Reference interpreter and the entry point. -/

def tinyRun (prog input : List UInt8) : List UInt8 :=
  let P := prog.toArray
  let n := P.size / 2
  let rec go (fuel pc i : Nat) (acc : UInt64) (out : List UInt8) : List UInt8 :=
    match fuel with
    | 0 => panic! "fuel"
    | fuel + 1 =>
      if pc ≥ n then out.reverse else
      let op := P[2 * pc]!; let a := P[2 * pc + 1]!
      let tgt : Nat := if a < 128 then pc + a.toNat else pc - (256 - a.toNat)
      if op == 0 then go fuel (pc + 1) i (acc + sx a) out
      else if op == 1 then go fuel (pc + 1) i (acc ^^^ sx a) out
      else if op == 2 then go fuel (pc + 1) (i + 1) (input[i]!).toUInt64 out
      else if op == 3 then go fuel (pc + 1) i acc (acc.toUInt8 :: out)
      else if op == 4 then go fuel (if acc != 0 then tgt else pc + 1) i acc out
      else if op == 5 then go fuel (pc + 1) i (input.length - i).toUInt64 out
      else if op == 6 then go fuel (if acc == 0 then tgt else pc + 1) i acc out
      else go fuel (pc + 1) i acc out
  go 10000000 0 0 0 []

def tinyCompile (xs : ByteArray) : List UInt8 := tc xs.data.toList
theorem tinyCompile_eq (xs : ByteArray) : tinyCompile xs = tc.view xs 0 := rfl
frontx_entry tinyCompile from tinyCompile_eq
-- plain fallback not well-formed (a loop of 1166 plain words): checked words
set_option maxHeartbeats 0 in
frontx_implements_listC tinyCompile

end Proven.Frontx.Tiny
