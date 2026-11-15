/- TINYSELF2, step 3: register allocation.  The stack machine of step 2 becomes three-address code over registers
r0, r1, ...: the register of a subexpression is its stack depth `d` (the word parameter `a` of `comp`; allocation by
depth: `bin k a b` puts `a` in r_d, `b` in r_(d+1), result in r_d).  `cnd c (alt t e)` evaluates c, t, e in
r_d, r_(d+1), r_(d+2) (so every child but the first is at d+1: an `if` in a call argument breaks `sem`, F9) and
`sel` writes r_d := if r_d ≠ 0 then r_(d+1) else r_(d+2).  The allocation is packed into the instruction scalar
(`k + d`, the SOURCE opcodes are pre-multiplied by 16: a shift or `16 * d` costs too much code, F1, and a helper
function for it does not get through `sem`, F7); `imm` carries a literal.  All scalars are `Nat`: a word literal at the entry works for `Nat` but
not for `UInt64` (F8); an entry with a word ARGUMENT from the input and a tree literal does not (F10).
Source `bin k a b`, k = 16 * (0 add, 1 sub, 2 xor, 3 ult, 4 eq, 5 seq, 6 set (b nil), 7 cnd (a = condition, b = `bin 8 t e`)). -/
import Riscv.Frontx.IndCmd

namespace Proven.Frontx.Tiny2S3

inductive T where
  | nil
  | lit (n : Nat)
  | var
  | bin (k : Nat) (a b : T)
  | op (k : Nat) (rest : T)

def comp : T → Nat → T → T
  | .nil, _, K => K
  | .lit n, d, K => .bin (144 + d) K (.lit n)
  | .var, d, K => .op (160 + d) K
  | .op k r, _, K => .op k r
  | .bin k a b, d, K => comp a d (comp b (d + 1) (.op (k + d) K))

def compile (e : T) : T := comp e 0 .nil

frontx_ind_type TT := T
frontx_ind compile on TT

/-! reference semantics (values mod 2^64) -/
def apply (k : Nat) (a b : UInt64) : UInt64 :=
  if k == 0 then a + b else if k == 1 then a - b else if k == 2 then a ^^^ b else if k == 3 then (if a < b then 1 else 0)
  else (if a == b then 1 else 0)

def ev : T → UInt64 → UInt64 × UInt64
  | .lit n, x => (UInt64.ofNat n, x)
  | .var, x => (x, x)
  | .bin k a b, x =>
    let k := k / 16
    if k < 5 then let (va, x1) := ev a x; let (vb, x2) := ev b x1; (apply k va vb, x2)
    else if k == 5 then let (_, x1) := ev a x; ev b x1
    else if k == 6 then let (v, _) := ev a x; (v, v)
    else match b with
      | .bin 128 t e => let (vc, x1) := ev a x; let (vt, x2) := ev t x1; let (ve, x3) := ev e x2
                      (if vc != 0 then vt else ve, x3)
      | _ => (0, x)
  | _, x => (0, x)
def eval (e : T) (x : UInt64) : UInt64 := (ev e x).1

/-- run the three-address code: registers r0.., x; result r0 -/
def run : T → UInt64 → List UInt64 → UInt64
  | .bin kk r imm, x, R =>
    let d := kk % 16; let k := kk / 16
    run r x (R.set d (match imm with | .lit n => UInt64.ofNat n | _ => 0))
  | .op kk r, x, R =>
    let d := kk % 16; let k := kk / 16
    let g := fun i => R.getD i 0
    if k < 5 then run r x (R.set d (apply k (g d) (g (d + 1))))
    else if k == 5 then run r x (R.set d (g (d + 1)))
    else if k == 6 then run r (g d) R
    else if k == 7 then run r x (R.set d (if g d != 0 then g (d + 1) else g (d + 2)))
    else if k == 8 then run r x R
    else run r x (R.set d x)
  | _, _, R => R.headD 0

end Proven.Frontx.Tiny2S3
