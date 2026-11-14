/- How Lean scalars and byte arrays sit in `BitVec 64` variables and heap blocks, and the lemma set the
generated per-function proofs rewrite with: every supported Lean operation, pushed through the
representation function (`r8`, `r32`, `r64`, `rN`), becomes a `BitVec 64` term over representations. -/
import Proven.Frontx.Tree

namespace Proven.Frontx
open Proven

def rN (n : Nat) : BitVec 64 := BitVec.ofNat 64 n
def r8 (x : UInt8) : BitVec 64 := x.toBitVec.setWidth 64
def r32 (x : UInt32) : BitVec 64 := x.toBitVec.setWidth 64
def r64 (x : UInt64) : BitVec 64 := x.toBitVec
/-- a `Bool` is `1` or `0` -/
def rB (b : Bool) : BitVec 64 := if b = true then 1 else 0
theorem rB_def (b : Bool) : rB b = if b = true then 1#64 else 0#64 := rfl
/-- the heap block of a byte array -/
def blk (xs : ByteArray) : List (BitVec 8) := xs.data.toList.map (·.toBitVec)

/-! ## heap -/
theorem rd0 (B : List (BitVec 8)) (H : Heap) (j : Nat) : rd (B :: H) 0 j = B[j]? := rfl
theorem rdS (B : List (BitVec 8)) (H : Heap) (b j : Nat) : rd (B :: H) (b + 1) j = rd H b j := rfl
theorem rd1 (B B' : List (BitVec 8)) (H : Heap) (j : Nat) : rd (B :: B' :: H) 1 j = B'[j]? := rfl
theorem rd2 (B B' B'' : List (BitVec 8)) (H : Heap) (j : Nat) : rd (B :: B' :: B'' :: H) 2 j = B''[j]? := rfl
theorem blk_get {xs : ByteArray} {i : Nat} (h : i < xs.size) : (blk xs)[i]? = some (xs[i]'h).toBitVec := by
  have h' : i < xs.data.toList.length := by simpa using h
  simp only [blk, List.getElem?_map, List.getElem?_eq_getElem h']; rfl
@[simp] theorem blk_length (xs : ByteArray) : (blk xs).length = xs.size := by simp [blk]
theorem r8_fold (x : UInt8) : x.toBitVec.setWidth 64 = r8 x := rfl
theorem ba_get! {xs : ByteArray} {i : Nat} (h : i < xs.size) : xs[i]! = xs[i]'h := getElem!_pos xs i h

/-! ## conditions: every translated condition denotes `if p then 1 else 0` -/
theorem c_not (p : Prop) [Decidable p] : (if p then 1 else 0 : BitVec 64) ^^^ 1 = if ¬p then 1 else 0 := by
  by_cases h : p <;> simp [h]
theorem c_and (p q : Prop) [Decidable p] [Decidable q] :
    (if p then 1 else 0 : BitVec 64) &&& (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases h : p <;> by_cases h' : q <;> simp [h, h']
theorem c_or (p q : Prop) [Decidable p] [Decidable q] :
    (if p then 1 else 0 : BitVec 64) ||| (if q then 1 else 0) = if p ∨ q then 1 else 0 := by
  by_cases h : p <;> by_cases h' : q <;> simp [h, h']
theorem c_eq0 (p : Prop) [Decidable p] : ((if p then 1 else 0 : BitVec 64) = 0) = ¬p := by
  by_cases h : p <;> simp [h]

/-- the same with the literals in `simp` normal form -/
theorem c_not' (p : Prop) [Decidable p] : (if p then 1#64 else 0#64) ^^^ 1#64 = if ¬p then 1#64 else 0#64 := c_not p
theorem c_and' (p q : Prop) [Decidable p] [Decidable q] :
    (if p then 1#64 else 0#64) &&& (if q then 1#64 else 0#64) = if p ∧ q then 1#64 else 0#64 := c_and p q
theorem c_or' (p q : Prop) [Decidable p] [Decidable q] :
    (if p then 1#64 else 0#64) ||| (if q then 1#64 else 0#64) = if p ∨ q then 1#64 else 0#64 := c_or p q
theorem c_eq0' (p : Prop) [Decidable p] : ((if p then 1#64 else 0#64) = 0#64) = ¬p := c_eq0 p

/-- a test is discharged in this form: the condition expression *is* the 0/1 value of the proposition -/
theorem ne0_of_c {x : BitVec 64} {p : Prop} [Decidable p] (h : x = if p then 1#64 else 0#64) : x ≠ 0#64 ↔ p := by
  subst h; by_cases hp : p <;> simp [hp]

/-! ## expression evaluation (used instead of unfolding `BExp.denote`, so that a select is rewritten in one
step and its condition is never negated) -/
def sel (c a b : BitVec 64) : BitVec 64 := if c = 0 then b else a
theorem denote_var (env : BEnv) (i : Nat) : (BExp.var i).denote env = env i := rfl
theorem denote_const (env : BEnv) (c : BitVec 64) : (BExp.const c).denote env = c := rfl
theorem denote_bin (env : BEnv) (op : Op) (a b : BExp) :
    (BExp.bin op a b).denote env = op.eval (a.denote env) (b.denote env) := rfl
theorem denote_ite (env : BEnv) (c a b : BExp) :
    (BExp.ite c a b).denote env = sel (c.denote env) (a.denote env) (b.denote env) := rfl
theorem sel_c (p : Prop) [Decidable p] (a b : BitVec 64) : sel (if p then 1#64 else 0#64) a b = if p then a else b := by
  by_cases h : p <;> simp [sel, h]

theorem sel_c' (p : Prop) [Decidable p] (a b : BitVec 64) : sel (if p then 0#64 else 1#64) a b = if p then b else a := by
  by_cases h : p <;> simp [sel, h]

/-- what `omega` is told about a temporary defined by an `if` -/
theorem ite_eq_or {c : Prop} [Decidable c] {a b x : Nat} (h : (if c then a else b) = x) : x = a ∨ x = b := by
  split at h <;> simp [← h]

/-! ## Nat (needs bounds: discharged by `omega` from the hypotheses) -/
theorem rN_toNat {n : Nat} (h : n < 2 ^ 64) : (rN n).toNat = n := by simp [rN]; omega
theorem rN_add (a b : Nat) : rN (a + b) = rN a + rN b := BitVec.ofNat_add a b
theorem rN_sub {a b : Nat} (h : b ≤ a) : rN (a - b) = rN a - rN b := by
  simp only [rN]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
/-- truncated subtraction, in general: a select -/
theorem rN_sub' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    rN (a - b) = if a < b then 0#64 else rN a - rN b := by
  by_cases h : a < b
  · rw [if_pos h, Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]; rfl
  · rw [if_neg h]; exact rN_sub (by omega)
/-- … and when `b ≤ a` is known the select disappears -/
theorem nat_ite_lt_neg {a b : Nat} (h : b ≤ a) (x y : BitVec 64) : (if a < b then x else y) = y :=
  if_neg (by omega)
theorem rN_succ (a : Nat) : rN (Nat.succ a) = rN a + 1#64 := rN_add a 1
theorem rN_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (rN a < rN b) = (a < b) := by
  simp [rN, BitVec.lt_def, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
theorem rN_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (rN a = rN b) = (a = b) := by
  simp [rN, ← BitVec.toNat_inj, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
theorem rN_eq_lit {a n : Nat} (ha : a < 2 ^ 64) (hn : n < 2 ^ 64) : (rN a = BitVec.ofNat 64 n) = (a = n) := rN_inj ha hn
theorem rN_lt_lit {a n : Nat} (ha : a < 2 ^ 64) (hn : n < 2 ^ 64) : (rN a < BitVec.ofNat 64 n) = (a < n) := rN_lt ha hn
theorem rN_lit_lt {a n : Nat} (ha : a < 2 ^ 64) (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n < rN a) = (n < a) := rN_lt hn ha
theorem rN_or (a b : Nat) : rN (a ||| b) = rN a ||| rN b := by
  apply BitVec.eq_of_toNat_eq; simp [rN, Nat.or_mod_two_pow]
theorem rN_and (a b : Nat) : rN (a &&& b) = rN a &&& rN b := by
  apply BitVec.eq_of_toNat_eq; simp [rN, Nat.and_mod_two_pow]
theorem rN_shl (a b : Nat) : rN (a <<< b) = rN a <<< b := by
  apply BitVec.eq_of_toNat_eq
  simp only [rN, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact (Nat.mod_mul_mod ..).symm
theorem rN_ite (p : Prop) [Decidable p] (a b : Nat) : rN (if p then a else b) = if p then rN a else rN b := by
  split <;> rfl

/-! ## UInt64 -/
theorem r64_add (a b : UInt64) : r64 (a + b) = r64 a + r64 b := rfl
theorem r64_sub (a b : UInt64) : r64 (a - b) = r64 a - r64 b := rfl
theorem r64_and (a b : UInt64) : r64 (a &&& b) = r64 a &&& r64 b := rfl
theorem r64_or (a b : UInt64) : r64 (a ||| b) = r64 a ||| r64 b := rfl
theorem r64_xor (a b : UInt64) : r64 (a ^^^ b) = r64 a ^^^ r64 b := rfl
theorem r64_ite (p : Prop) [Decidable p] (a b : UInt64) : r64 (if p then a else b) = if p then r64 a else r64 b := by
  split <;> rfl
theorem r64_inj (a b : UInt64) : (r64 a = r64 b) = (a = b) := by simp [r64, UInt64.toBitVec_inj]
theorem r64_lt (a b : UInt64) : (r64 a < r64 b) = (a < b) := by simp [r64, UInt64.lt_iff_toBitVec_lt]
/-- comparisons of fixed-width values are moved to the `BitVec 64` level (hypotheses and goal alike) -/
theorem r64_eq' (a b : UInt64) : (a = b) = (r64 a = r64 b) := (r64_inj a b).symm
theorem r64_lt' (a b : UInt64) : (a < b) = (r64 a < r64 b) := (r64_lt a b).symm
theorem r64_le' (a b : UInt64) : (a ≤ b) = ¬(r64 b < r64 a) := by rw [r64_lt]; exact propext UInt64.not_lt.symm
theorem r64_toNat (a : UInt64) : rN a.toNat = r64 a := by simp [rN, r64]
theorem r64_ofNat (n : Nat) : r64 n.toUInt64 = rN n := by simp [rN, r64, Nat.toUInt64, UInt64.ofNat]

/-! ## UInt32 and UInt8: zero-extended; `+`, `-`, `<<<` are followed by a mask -/
theorem and_mask32 (x : BitVec 64) : (x &&& 0xffffffff#64).toNat = x.toNat % 2 ^ 32 := by
  rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 32
theorem and_mask8 (x : BitVec 64) : (x &&& 0xff#64).toNat = x.toNat % 2 ^ 8 := by
  rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 8
theorem r32_nat (a : UInt32) : (r32 a).toNat = a.toNat := by
  have := a.toBitVec.isLt; simp only [r32, BitVec.toNat_setWidth, UInt32.toNat_toBitVec] at *; omega
theorem r8_nat (a : UInt8) : (r8 a).toNat = a.toNat := by
  have := a.toBitVec.isLt; simp only [r8, BitVec.toNat_setWidth, UInt8.toNat_toBitVec] at *; omega

theorem r32_add (a b : UInt32) : r32 (a + b) = (r32 a + r32 b) &&& 0xffffffff#64 := by
  apply BitVec.eq_of_toNat_eq
  have := a.toNat_lt; have := b.toNat_lt
  rw [and_mask32, BitVec.toNat_add, r32_nat, r32_nat, r32_nat, UInt32.toNat_add]; omega
theorem r32_sub (a b : UInt32) : r32 (a - b) = (r32 a - r32 b) &&& 0xffffffff#64 := by
  apply BitVec.eq_of_toNat_eq
  have := a.toNat_lt; have := b.toNat_lt
  rw [and_mask32, BitVec.toNat_sub, r32_nat, r32_nat, r32_nat, UInt32.toNat_sub]; omega
theorem r32_and (a b : UInt32) : r32 (a &&& b) = r32 a &&& r32 b := by simp [r32, BitVec.setWidth_and]
theorem r32_or (a b : UInt32) : r32 (a ||| b) = r32 a ||| r32 b := by simp [r32, BitVec.setWidth_or]
theorem r32_xor (a b : UInt32) : r32 (a ^^^ b) = r32 a ^^^ r32 b := by simp [r32, BitVec.setWidth_xor]
theorem r32_ite (p : Prop) [Decidable p] (a b : UInt32) : r32 (if p then a else b) = if p then r32 a else r32 b := by
  split <;> rfl
theorem r32_inj (a b : UInt32) : (r32 a = r32 b) = (a = b) := by
  rw [← BitVec.toNat_inj, r32_nat, r32_nat, UInt32.toNat_inj]
theorem r32_lt (a b : UInt32) : (r32 a < r32 b) = (a < b) := by
  rw [BitVec.lt_def, r32_nat, r32_nat, UInt32.lt_iff_toNat_lt]
theorem r32_eq' (a b : UInt32) : (a = b) = (r32 a = r32 b) := (r32_inj a b).symm
theorem r32_lt' (a b : UInt32) : (a < b) = (r32 a < r32 b) := (r32_lt a b).symm
theorem r32_le' (a b : UInt32) : (a ≤ b) = ¬(r32 b < r32 a) := by rw [r32_lt]; exact propext UInt32.not_lt.symm
theorem r32_toNat (a : UInt32) : rN a.toNat = r32 a := by
  apply BitVec.eq_of_toNat_eq; have := a.toNat_lt; rw [r32_nat]; simp [rN]
theorem r32_shr (a b : UInt32) : r32 (a >>> b) = r32 a >>> ((r32 b &&& 31#64).toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  have h : (r32 b &&& 31#64).toNat = b.toNat % 2 ^ 5 := by
    rw [BitVec.toNat_and, r32_nat]; exact Nat.and_two_pow_sub_one_eq_mod _ 5
  rw [h, BitVec.toNat_ushiftRight, r32_nat, r32_nat, UInt32.toNat_shiftRight]
  congr 1; omega

theorem r8_add (a b : UInt8) : r8 (a + b) = (r8 a + r8 b) &&& 0xff#64 := by
  apply BitVec.eq_of_toNat_eq
  have := a.toNat_lt; have := b.toNat_lt
  rw [and_mask8, BitVec.toNat_add, r8_nat, r8_nat, r8_nat, UInt8.toNat_add]; omega
theorem r8_sub (a b : UInt8) : r8 (a - b) = (r8 a - r8 b) &&& 0xff#64 := by
  apply BitVec.eq_of_toNat_eq
  have := a.toNat_lt; have := b.toNat_lt
  rw [and_mask8, BitVec.toNat_sub, r8_nat, r8_nat, r8_nat, UInt8.toNat_sub]; omega
theorem r8_and (a b : UInt8) : r8 (a &&& b) = r8 a &&& r8 b := by simp [r8, BitVec.setWidth_and]
theorem r8_or (a b : UInt8) : r8 (a ||| b) = r8 a ||| r8 b := by simp [r8, BitVec.setWidth_or]
theorem r8_xor (a b : UInt8) : r8 (a ^^^ b) = r8 a ^^^ r8 b := by simp [r8, BitVec.setWidth_xor]
theorem r8_ite (p : Prop) [Decidable p] (a b : UInt8) : r8 (if p then a else b) = if p then r8 a else r8 b := by
  split <;> rfl
theorem r8_inj (a b : UInt8) : (r8 a = r8 b) = (a = b) := by
  rw [← BitVec.toNat_inj, r8_nat, r8_nat, UInt8.toNat_inj]
theorem r8_lt (a b : UInt8) : (r8 a < r8 b) = (a < b) := by
  rw [BitVec.lt_def, r8_nat, r8_nat, UInt8.lt_iff_toNat_lt]
theorem r8_eq' (a b : UInt8) : (a = b) = (r8 a = r8 b) := (r8_inj a b).symm
theorem r8_lt' (a b : UInt8) : (a < b) = (r8 a < r8 b) := (r8_lt a b).symm
theorem r8_le' (a b : UInt8) : (a ≤ b) = ¬(r8 b < r8 a) := by rw [r8_lt]; exact propext UInt8.not_lt.symm
theorem r8_toNat (a : UInt8) : rN a.toNat = r8 a := by
  apply BitVec.eq_of_toNat_eq; have := a.toNat_lt; rw [r8_nat]; simp [rN]

/-! ## conversions -/
theorem r32_of8 (a : UInt8) : r32 a.toUInt32 = r8 a := by
  apply BitVec.eq_of_toNat_eq; rw [r32_nat, r8_nat, UInt8.toNat_toUInt32]
theorem r64_of8 (a : UInt8) : r64 a.toUInt64 = r8 a := by
  apply BitVec.eq_of_toNat_eq; rw [r8_nat]; simp [r64]
theorem r64_of32 (a : UInt32) : r64 a.toUInt64 = r32 a := by
  apply BitVec.eq_of_toNat_eq; rw [r32_nat]; simp [r64]
theorem r8_of32 (a : UInt32) : r8 a.toUInt8 = r32 a &&& 0xff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask8, r8_nat, r32_nat, UInt32.toNat_toUInt8]
theorem r32_of64 (a : UInt64) : r32 a.toUInt32 = r64 a &&& 0xffffffff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask32, r32_nat, UInt64.toNat_toUInt32]; rfl
theorem r8_of64 (a : UInt64) : r8 a.toUInt8 = r64 a &&& 0xff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask8, r8_nat, UInt64.toNat_toUInt8]; rfl
theorem r8_ofNat (n : Nat) : r8 n.toUInt8 = rN n &&& 0xff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask8, r8_nat]; simp [rN]
theorem r32_ofNat (n : Nat) : r32 n.toUInt32 = rN n &&& 0xffffffff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask32, r32_nat]; simp [rN]

/-! ## dependent `if` -/
theorem r8_dite (p : Prop) [Decidable p] (a : p → UInt8) (b : ¬p → UInt8) :
    r8 (dite p a b) = dite p (fun h => r8 (a h)) (fun h => r8 (b h)) := by split <;> rfl
theorem r32_dite (p : Prop) [Decidable p] (a : p → UInt32) (b : ¬p → UInt32) :
    r32 (dite p a b) = dite p (fun h => r32 (a h)) (fun h => r32 (b h)) := by split <;> rfl
theorem r64_dite (p : Prop) [Decidable p] (a : p → UInt64) (b : ¬p → UInt64) :
    r64 (dite p a b) = dite p (fun h => r64 (a h)) (fun h => r64 (b h)) := by split <;> rfl
theorem rN_dite (p : Prop) [Decidable p] (a : p → Nat) (b : ¬p → Nat) :
    rN (dite p a b) = dite p (fun h => rN (a h)) (fun h => rN (b h)) := by split <;> rfl

/-! ## literals -/
theorem rN_lit (n : Nat) : rN (no_index (OfNat.ofNat n)) = BitVec.ofNat 64 n := rfl
theorem r8_lit (n : Nat) : r8 (no_index (OfNat.ofNat n)) = BitVec.ofNat 64 (n % 256) := by
  apply BitVec.eq_of_toNat_eq; rw [r8_nat]; simp [OfNat.ofNat, UInt8.toNat_ofNat']
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt n (by decide)) (by decide))).symm
theorem r32_lit (n : Nat) : r32 (no_index (OfNat.ofNat n)) = BitVec.ofNat 64 (n % 4294967296) := by
  apply BitVec.eq_of_toNat_eq; rw [r32_nat]; simp [OfNat.ofNat, UInt32.toNat_ofNat']
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt n (by decide)) (by decide))).symm
theorem r64_lit (n : Nat) : r64 (no_index (OfNat.ofNat n)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp [r64, OfNat.ofNat, UInt64.toNat_ofNat']

end Proven.Frontx
