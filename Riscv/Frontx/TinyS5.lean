/- TINYSELF2, step 5: real RV64 encodings.  The compiler emits 32-bit RV64 words (the scalar of `op w`; the low 32
bits are the instruction) for LEFT-DEEP pure expressions over `x` (a0): the right operand of `bin` is a leaf, the left
result lives in x16, the right leaf is loaded into x17, `op x16, x16, x17`; x16 is the result.  General register
allocation by depth would need the register number shifted into three fields of the word (d << 7, d << 15,
(d + 1) << 20): the front end has no shifts, and `+` doublings do not get through (13 of them: `simp` runs out of steps
in `sem`, F15; fewer: code size, F1).  With two registers the only variable field is `rd` of a leaf load, and the word
parameter is 0 (left, x16) or 128 (right, x17): `rd << 7` without a shift.  The source supplies what would need a shift:
literals as `imm << 20` and the operator as its funct bits (add 0, sub 0x40000000, xor 0x4000, sltu 0x3000).
`mv a0, x16` (0x00080513) and `ret` (0x00008067) are appended by the harness (the entry's tree argument must be
nullary). -/
import Riscv.Frontx.IndCmd

namespace Proven.Frontx.Tiny2S5

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
  | .bin k a b, w, K => comp a 0 (comp b 128 (.op (k + 18352179) K))

def compile (e : T) : T := comp e 0 .nil   -- the entry's tree argument must be nullary (F2'): the harness appends `mv a0, x16; ret`

frontx_ind_type TT := T
set_option maxHeartbeats 0 in
frontx_ind compile on TT

/-- reference semantics of a source (literals are `imm << 20`, `imm < 2048`) -/
def eval (x : UInt64) : T → UInt64
  | .lit n => UInt64.ofNat (n / 1048576)
  | .var => x
  | .bin k a b =>
    let va := eval x a; let vb := eval x b
    if k == 0 then va + vb else if k == 1073741824 then va - vb else if k == 16384 then va ^^^ vb
    else if va < vb then 1 else 0
  | _ => 0

end Proven.Frontx.Tiny2S5
