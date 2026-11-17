import Nano.Gen
import Nano.V2Ast
/- nano v2 stack generator, increments 1 and 2.  Same records, registers, calling convention and `asm` as v1
(`Nano/Gen.lean`): NO new instruction.  `if a ⋈ b then t else e` is computed without branches (nano is pure and
total, so evaluating both branches gives Lean's value):
  X, then c := (a ⋈' b) ∈ {0, 1}, then Y, then X + c * (Y - X)
with (X, Y) = (e, t) for `==`/`<` and (t, e) for `<=` (`a <= b` = not `b < a`, so c := b < a).  `<` on words is
computed with shifts and arithmetic only (`ltuOps`, see `Nano/V2Rec.lean` `ltu_bits`):
  a <u b = ((a >> 1) - (b >> 1) - (b & 1) * (1 - (a & 1))) >> 63,   x & 1 = x - (x >> 1) * 2,
signed `<` is unsigned `<` after adding 2^63 to both, `a == b` is `(a - b) <u 1`.  The stack operations (`SOp`)
are short fixed record sequences over the v1 record families.  Branching code arrives with loops (increment 4).
Increment 2: `|||` is v1's OR record, shifts are v1's SLLI/SRLI records, `&&&` and `^^^` are computed from `+ - |||`. -/
namespace Nano.V2
open Nano (r ld sd addSp push li binop mkSc rd8 pro wr8 asm)

/-- stack operations; `j`, `k` small -/
inductive SOp where
  | dup (j : Nat)      -- push the `j`-th value from the top
  | shr (k : Nat)      -- top := top >>> k
  | bin (k : Nat)      -- pop b, a; push a ∘ b (24 add, 32 sub, 40 mul)
  | lit (n : UInt64)   -- push n
  | slide (k : Nat)    -- drop the k values below the top
  | bor                -- pop b, a; push a ||| b (increment 2)
  | shl (k : Nat)      -- top := top <<< k (increment 2)

def SOp.code : SOp → List UInt8
  | .dup j => ld 5 31 j ++ push
  | .shr k => ld 5 31 0 ++ r 5 6 5 k.toUInt8 ++ r 0 5 0 0 ++ r 24 5 5 6 ++ sd 5 31 0
  | .bin k => binop k.toUInt8
  | .lit n => li n ++ push
  | .slide k => ld 5 31 0 ++ addSp k ++ sd 5 31 0
  | .bor => binop 14
  | .shl k => ld 5 31 0 ++ r 1 5 5 k.toUInt8 ++ sd 5 31 0

def opsCode : List SOp → List UInt8
  | [] => []
  | o :: os => o.code ++ opsCode os

/-- `b, a ↦ a <u b` (top first) -/
def ltuOps : List SOp :=
  [.dup 1, .shr 1, .dup 1, .shr 1, .bin 32,
   .dup 1, .dup 0, .shr 1, .lit 2, .bin 40, .bin 32,
   .dup 3, .dup 0, .shr 1, .lit 2, .bin 40, .bin 32,
   .dup 1, .bin 40, .bin 32, .bin 32, .shr 63, .slide 2]

/-- `b, a ↦ a <s b` -/
def ltsOps : List SOp :=
  [.dup 1, .lit 0x8000000000000000, .bin 24, .dup 1, .lit 0x8000000000000000, .bin 24] ++ ltuOps ++ [.slide 2]

/-- `b, a ↦ a == b` -/
def eqOps : List SOp := [.bin 32, .lit 1] ++ ltuOps

/-- `Y, c, X ↦ X + c * (Y - X)` -/
def selOps : List SOp := [.dup 2, .bin 32, .bin 40, .bin 24]

/-- `b, a ↦ a &&& b` = `(a + b) - (a ||| b)` (increment 2; `Nano.V2R.and_eq_add_sub_or`) -/
def andOps : List SOp := [.dup 1, .dup 1, .bin 24, .dup 2, .dup 2, .bor, .bin 32, .slide 2]

/-- `b, a ↦ a ^^^ b` = `(a ||| b) - (a &&& b)` -/
def xorOps : List SOp := [.dup 1, .dup 1, .bor, .dup 2, .dup 2] ++ andOps ++ [.bin 32, .slide 2]

def bitOps : BOp → List SOp
  | .and => andOps
  | .or => [.bor]
  | .xor => xorOps

def shOp (l : Bool) (k : Nat) : SOp := if l then .shl k else .shr k

/-- the comparison ops of a kind (applied to the operands in `cmpArgs` order) -/
def cmpOps : Cmp → List SOp
  | .eq => eqOps
  | .ltu | .leu => ltuOps
  | .lts | .les => ltsOps

/-- `<=` swaps: `a <= b` = not (`b < a`) -/
def Cmp.swap : Cmp → Bool
  | .leu | .les => true
  | _ => false

/-- the peak stack height of `ops` started at height `h` -/
def SOp.peak (h : Nat) : SOp → Nat
  | .dup _ | .lit _ => h + 1
  | _ => h
def SOp.after (h : Nat) : SOp → Nat
  | .dup _ | .lit _ => h + 1
  | .bin _ | .bor => h - 1
  | .slide k => h - k
  | .shr _ | .shl _ => h
def peakOps (h : Nat) : List SOp → Nat
  | [] => h
  | o :: os => max (o.peak h) (peakOps (o.after h) os)

def cnt : E → Nat
  | .acons _ r => cnt r + 1
  | _ => 0

mutual
def genE : List Nat → Nat → E → List UInt8
  | _, _, .num n => li n ++ push
  | sc, d, .var i => ld 5 31 (d - 1 - sc.getD i 0) ++ push
  | sc, d, .add a b => genE sc d a ++ genE sc (d + 1) b ++ binop 24
  | sc, d, .sub a b => genE sc d a ++ genE sc (d + 1) b ++ binop 32
  | sc, d, .mul a b => genE sc d a ++ genE sc (d + 1) b ++ binop 40
  | sc, d, .let_ v b => genE sc d v ++ genE (d :: sc) (d + 1) b ++ ld 5 31 0 ++ addSp 1 ++ sd 5 31 0
  | sc, d, .call b as =>
    genA sc d as ++ genE (mkSc (cnt as) d) (d + cnt as) b ++ ld 5 31 0 ++ addSp (cnt as) ++ sd 5 31 0
  | sc, d, .ite k a b t e =>
    if k.swap then
      genE sc d t ++ genE sc (d + 1) b ++ genE sc (d + 2) a ++ opsCode (cmpOps k) ++ genE sc (d + 2) e ++ opsCode selOps
    else
      genE sc d e ++ genE sc (d + 1) a ++ genE sc (d + 2) b ++ opsCode (cmpOps k) ++ genE sc (d + 2) t ++ opsCode selOps
  | sc, d, .bit o a b => genE sc d a ++ genE sc (d + 1) b ++ opsCode (bitOps o)
  | sc, d, .sh l k a => genE sc d a ++ opsCode [shOp l (k % 64)]
  | _, _, _ => []
def genA : List Nat → Nat → E → List UInt8
  | sc, d, .acons e r => genE sc d e ++ genA sc (d + 1) r
  | _, _, _ => []
end

def genR (p : Prog) : List UInt8 :=
  r 5 31 2 3 ++ r 1 31 31 3 ++ r 0 28 10 0 ++ pro p.1 ++ genE (mkSc p.1 0) p.1 p.2 ++ ld 5 31 0 ++ wr8 ++ r 48 0 1 0

mutual
def depE : Nat → E → Nat
  | d, .num _ => d + 1
  | d, .var _ => d + 1
  | d, .add a b => max (depE d a) (depE (d + 1) b)
  | d, .sub a b => max (depE d a) (depE (d + 1) b)
  | d, .mul a b => max (depE d a) (depE (d + 1) b)
  | d, .let_ v b => max (depE d v) (depE (d + 1) b)
  | d, .call b as => max (depA d as) (depE (d + cnt as) b)
  | d, .ite k a b t e =>
    if k.swap then
      max (depE d t) (max (depE (d + 1) b) (max (depE (d + 2) a) (max (peakOps (d + 3) (cmpOps k))
        (max (depE (d + 2) e) (peakOps (d + 3) selOps)))))
    else
      max (depE d e) (max (depE (d + 1) a) (max (depE (d + 2) b) (max (peakOps (d + 3) (cmpOps k))
        (max (depE (d + 2) t) (peakOps (d + 3) selOps)))))
  | d, .bit o a b => max (depE d a) (max (depE (d + 1) b) (peakOps (d + 2) (bitOps o)))
  | d, .sh _ _ a => depE d a
  | _, _ => 0
def depA : Nat → E → Nat
  | d, .acons e r => max (depE d e) (depA (d + 1) r)
  | _, _ => 0
end
def depth (p : Prog) : Nat := max p.1 (depE p.1 p.2)

/-- **the v2 code generator** -/
def nanoGen (p : Prog) : List UInt8 := asm (genR p)

end Nano.V2
