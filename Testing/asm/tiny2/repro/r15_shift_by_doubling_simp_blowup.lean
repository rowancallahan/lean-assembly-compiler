/- TINYSELF2, step 5: real RV64 encodings.  The compiler emits 32-bit RV64 words (the scalar of `op w`; the low 32
bits are the instruction) for pure expressions over `x` (a0), registers x16.. (a6, a7, s2..: the register of a
subexpression is 16 + its depth), result in x16.  There are no shifts in the front end (F1/F7: a shift as `+`
doublings costs code, a helper function does not get through `sem`), so the encodings are built by additions only:
the word parameter carries `w = 128 d`, so `rd` of `addi` is `w` (+ constants) and the fields of an R-type word
(rd = rs1 = 16 + d, rs2 = 17 + d, i.e. d * 1081472 = 8449 w) come from `w + (w << 8) + (w << 13)`, 13 doublings in
one arm.  The source supplies what would need a shift anyway: literals as `imm << 20` and the operator as its
funct bits (add 0, sub 0x40000000, xor 0x4000, sltu 0x3000); the compiler adds the opcode, register and
constant fields.  `mv a0, x16` (0x00080513) and `ret` (0x00008067) are appended by the harness. -/
import Riscv.Frontx.IndCmd

namespace R15

inductive T where
  | nil
  | lit (n : Nat)               -- n = imm << 20, imm a 12-bit immediate
  | var
  | bin (k : Nat) (a b : T)     -- k = funct bits
  | op (w : Nat) (rest : T)

def comp : T → Nat → T → T
  | .nil, _, K => K
  | .lit n, w, K => .op (n + w + 2067) K
  | .var, w, K => .op (w + 329747) K
  | .op x r, _, K => .op x r
  | .bin k a b, w, K =>
    let s1 := w + w
    let s2 := s1 + s1
    let s3 := s2 + s2
    let s4 := s3 + s3
    let s5 := s4 + s4
    let s6 := s5 + s5
    let s7 := s6 + s6
    let s8 := s7 + s7
    let s9 := s8 + s8
    let s10 := s9 + s9
    let s11 := s10 + s10
    let s12 := s11 + s11
    let s13 := s12 + s12
    comp a w (comp b (w + 128) (.op (k + 18352179 + w + s8 + s13) K))

def compile (e : T) : T := comp e 0 .nil   -- the entry's tree argument must be nullary (F2'): the harness appends `mv a0, x16; ret`

frontx_ind_type TT := T
set_option maxHeartbeats 0 in
frontx_ind compile on TT

end R15
