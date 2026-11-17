/- Stage 2 split in two (owner: ≤ 5 min per compiled stage; `Testing/notes/NANO_PARSE_S3.md`):
* 2a (`stage2a`, box session_01MfKuVd8zxJmc6ZVj9VyJmH): stage 1's bytes → the tokens in a simple tag format
  (`encT (decL bs)`);
* 2b (`stage2b`, here): the tag format → the parser machine's output (`runS`, Nano/ParseS3.lean).
`stage2b_stage2a : stage2b (stage2a bs) = stage2 bs` on every input.

Tag format (`encT`): `none` ↦ `[]`; `some (b, ts)` ↦ `(if b then 2 else 1) :: tokens`; a token: `kdef` 1, `klet` 2,
`kty false` 3, `kty true` 4, `num n` 5 and 8 bytes little-endian, `lp` 6, `rp` 7, `colon` 8, `assign` 9, `plus` 10,
`minus` 11, `star` 12, `semi` 13, `id s` 14, then `[1, c]` per character, then `0`. -/
import Nano.ParseS3

namespace Nano.PS
open Nano Nano.B Nano.PB

/-! ## the format -/

def encId : List UInt8 → List UInt8
  | [] => [0]
  | c :: s => 1 :: c :: encId s

def le8 (n : UInt64) : List UInt8 :=
  [n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8, (n >>> 32).toUInt8, (n >>> 40).toUInt8,
    (n >>> 48).toUInt8, (n >>> 56).toUInt8]

def encTok : Tok → List UInt8
  | .kdef => [1] | .klet => [2] | .kty false => [3] | .kty true => [4]
  | .num n => 5 :: le8 n
  | .lp => [6] | .rp => [7] | .colon => [8] | .assign => [9] | .plus => [10] | .minus => [11] | .star => [12]
  | .semi => [13]
  | .id s => 14 :: encId s

def encToks : List Tok → List UInt8
  | [] => []
  | t :: ts => encTok t ++ encToks ts

/-- **the format between 2a and 2b** -/
def encT : Option (Bool × List Tok) → List UInt8
  | none => []
  | some (b, ts) => (if b then 2 else 1) :: encToks ts

/-- **stage 2a** (its S3 form and compile: box session_01MfKuVd8zxJmc6ZVj9VyJmH) -/
def stage2a (bs : List UInt8) : List UInt8 := encT (decL bs)

/-! ## the decoder of 2b (structural) -/

/-- a word from 8 little-endian bytes -/
def w8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  b0.toUInt64 + 256 * (b1.toUInt64 + 256 * (b2.toUInt64 + 256 * (b3.toUInt64 + 256 * (b4.toUInt64 +
    256 * (b5.toUInt64 + 256 * (b6.toUInt64 + 256 * b7.toUInt64))))))

theorem w8_le8 (n : UInt64) :
    w8 n.toUInt8 (n >>> 8).toUInt8 (n >>> 16).toUInt8 (n >>> 24).toUInt8 (n >>> 32).toUInt8 (n >>> 40).toUInt8
      (n >>> 48).toUInt8 (n >>> 56).toUInt8 = n := by
  apply UInt64.toNat_inj.mp
  have h := n.toNat_lt
  simp only [w8, UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8,
    UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow]
  omega

/-- the tokens; `some acc`: inside an identifier (characters so far, newest first) -/
def decT2 : List UInt8 → Option (List UInt8) → Option (List Tok)
  | [], none => some []
  | [], some _ => none
  | b :: r, some acc =>
    if b == 0 then consO (.id acc.reverse) (decT2 r none)
    else if b == 1 then
      match r with
      | c :: r' => decT2 r' (some (c :: acc))
      | [] => none
    else none
  | t :: r, none =>
    if t == 1 then consO .kdef (decT2 r none)
    else if t == 2 then consO .klet (decT2 r none)
    else if t == 3 then consO (.kty false) (decT2 r none)
    else if t == 4 then consO (.kty true) (decT2 r none)
    else if t == 6 then consO .lp (decT2 r none)
    else if t == 7 then consO .rp (decT2 r none)
    else if t == 8 then consO .colon (decT2 r none)
    else if t == 9 then consO .assign (decT2 r none)
    else if t == 10 then consO .plus (decT2 r none)
    else if t == 11 then consO .minus (decT2 r none)
    else if t == 12 then consO .star (decT2 r none)
    else if t == 13 then consO .semi (decT2 r none)
    else if t == 14 then decT2 r (some [])
    else if t == 5 then
      match r with
      | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r' => consO (.num (w8 b0 b1 b2 b3 b4 b5 b6 b7)) (decT2 r' none)
      | _ => none
    else none

/-- `decL` in the tag format -/
def decLT : List UInt8 → Option (Bool × List Tok)
  | b :: r => if b == 1 then pairO false (decT2 r none) else if b == 2 then pairO true (decT2 r none) else none
  | [] => none

theorem dT1 (r : List UInt8) : decT2 (1 :: r) none = consO .kdef (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT2 (r : List UInt8) : decT2 (2 :: r) none = consO .klet (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT3 (r : List UInt8) : decT2 (3 :: r) none = consO (.kty false) (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT4 (r : List UInt8) : decT2 (4 :: r) none = consO (.kty true) (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT6 (r : List UInt8) : decT2 (6 :: r) none = consO .lp (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT7 (r : List UInt8) : decT2 (7 :: r) none = consO .rp (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT8 (r : List UInt8) : decT2 (8 :: r) none = consO .colon (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT9 (r : List UInt8) : decT2 (9 :: r) none = consO .assign (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT10 (r : List UInt8) : decT2 (10 :: r) none = consO .plus (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT11 (r : List UInt8) : decT2 (11 :: r) none = consO .minus (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT12 (r : List UInt8) : decT2 (12 :: r) none = consO .star (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT13 (r : List UInt8) : decT2 (13 :: r) none = consO .semi (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dT14 (r : List UInt8) : decT2 (14 :: r) none = decT2 r (some []) := by
  rw [decT2.eq_def]; rfl
theorem dT5 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (r : List UInt8) :
    decT2 (5 :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r) none =
      consO (.num (w8 b0 b1 b2 b3 b4 b5 b6 b7)) (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dI0 (acc r : List UInt8) : decT2 (0 :: r) (some acc) = consO (.id acc.reverse) (decT2 r none) := by
  rw [decT2.eq_def]; rfl
theorem dI1 (c : UInt8) (acc r : List UInt8) : decT2 (1 :: c :: r) (some acc) = decT2 r (some (c :: acc)) := by
  rw [decT2.eq_def]; rfl

theorem decT2_id : ∀ (s acc : List UInt8) (rest : List UInt8),
    decT2 (encId s ++ rest) (some acc) = consO (.id (acc.reverse ++ s)) (decT2 rest none)
  | [], acc, rest => by simp only [encId, List.cons_append, List.nil_append, dI0, List.append_nil]
  | c :: s, acc, rest => by
    simp only [encId, List.cons_append, dI1]
    rw [decT2_id s (c :: acc) rest]
    simp

theorem decT2_toks : ∀ ts : List Tok, decT2 (encToks ts) none = some ts
  | [] => rfl
  | t :: ts => by
    have ih := decT2_toks ts
    cases t with
    | id s =>
      simp only [encToks, encTok, List.cons_append, dT14]
      rw [decT2_id s [] (encToks ts), ih]; rfl
    | num n =>
      simp only [encToks, encTok, le8, List.cons_append, List.nil_append, dT5]
      rw [w8_le8, ih]; rfl
    | kty b => cases b <;> simp only [encToks, encTok, List.cons_append, List.nil_append, dT3, dT4, ih, consO]
    | _ => simp only [encToks, encTok, List.cons_append, List.nil_append, dT1, dT2, dT6, dT7, dT8, dT9, dT10, dT11,
        dT12, dT13, ih, consO]

/-- **stage 2b, S3 form**: the parser machine on the tag format -/
def stage2b (bs : List UInt8) : List UInt8 :=
  match decLT bs with
  | some (_, ts) => (runS (gasS ts) (.defs (ts.length + 1)) ⟨ts, [], 0, [], [], [], [], 0, 0⟩).getD []
  | none => []

theorem decLT_nil : decLT [] = none := rfl

/-- **the bridge of the split**: 2b after 2a is stage 2, on every input -/
theorem stage2b_stage2a (bs : List UInt8) : stage2b (stage2a bs) = stage2 bs := by
  rw [← stage2S_eq]
  unfold stage2b stage2a stage2S
  rw [decLS_eq]
  cases h : decL bs with
  | none => rfl
  | some p =>
    obtain ⟨b, ts⟩ := p
    have : decLT (encT (some (b, ts))) = some (b, ts) := by
      cases b <;> simp [encT, decLT, decT2_toks, pairO]
    rw [this]

end Nano.PS
