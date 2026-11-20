/- Round 7 (source level, once): `UInt16` scalars, `Except` / `Option` results with compound payloads as
components, and the `bind` lemmas the normalised equations of `do` code are proved with.

An `Except ε α` result is the tag `excTag` (`true` = `ok`) and the components of the payload (`excGet π z`:
the component `π` of the `ok` value, `z` on `error`); the error value itself is not kept.  `Option α` the same
with `Option.isSome` and `optGet`. -/
import Legacy.Riscv.Frontx.Rep

namespace Proven.Frontx
open Proven

/-! ## `UInt16`: zero-extended, `+`, `-`, `<<<` followed by a mask -/
def r16 (x : UInt16) : BitVec 64 := x.toBitVec.setWidth 64

theorem and_mask16 (x : BitVec 64) : (x &&& 0xffff#64).toNat = x.toNat % 2 ^ 16 := by
  rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 16
theorem r16_nat (a : UInt16) : (r16 a).toNat = a.toNat := by
  have := a.toBitVec.isLt; simp only [r16, BitVec.toNat_setWidth, UInt16.toNat_toBitVec] at *; omega
theorem r16_add (a b : UInt16) : r16 (a + b) = (r16 a + r16 b) &&& 0xffff#64 := by
  apply BitVec.eq_of_toNat_eq
  have := a.toNat_lt; have := b.toNat_lt
  rw [and_mask16, BitVec.toNat_add, r16_nat, r16_nat, r16_nat, UInt16.toNat_add]; omega
theorem r16_sub (a b : UInt16) : r16 (a - b) = (r16 a - r16 b) &&& 0xffff#64 := by
  apply BitVec.eq_of_toNat_eq
  have := a.toNat_lt; have := b.toNat_lt
  rw [and_mask16, BitVec.toNat_sub, r16_nat, r16_nat, r16_nat, UInt16.toNat_sub]; omega
theorem r16_and (a b : UInt16) : r16 (a &&& b) = r16 a &&& r16 b := by simp [r16, BitVec.setWidth_and]
theorem r16_or (a b : UInt16) : r16 (a ||| b) = r16 a ||| r16 b := by simp [r16, BitVec.setWidth_or]
theorem r16_xor (a b : UInt16) : r16 (a ^^^ b) = r16 a ^^^ r16 b := by simp [r16, BitVec.setWidth_xor]
theorem r16_ite (p : Prop) [Decidable p] (a b : UInt16) : r16 (if p then a else b) = if p then r16 a else r16 b := by
  split <;> rfl
theorem r16_dite (p : Prop) [Decidable p] (a : p → UInt16) (b : ¬p → UInt16) :
    r16 (dite p a b) = dite p (fun h => r16 (a h)) (fun h => r16 (b h)) := by split <;> rfl
theorem r16_inj (a b : UInt16) : (r16 a = r16 b) = (a = b) := by
  rw [← BitVec.toNat_inj, r16_nat, r16_nat, UInt16.toNat_inj]
theorem r16_lt (a b : UInt16) : (r16 a < r16 b) = (a < b) := by
  rw [BitVec.lt_def, r16_nat, r16_nat, UInt16.lt_iff_toNat_lt]
theorem r16_eq' (a b : UInt16) : (a = b) = (r16 a = r16 b) := (r16_inj a b).symm
theorem r16_lt' (a b : UInt16) : (a < b) = (r16 a < r16 b) := (r16_lt a b).symm
theorem r16_le' (a b : UInt16) : (a ≤ b) = ¬(r16 b < r16 a) := by rw [r16_lt]; exact propext UInt16.not_lt.symm
theorem r16_toNat (a : UInt16) : rN a.toNat = r16 a := by
  apply BitVec.eq_of_toNat_eq; have := a.toNat_lt; rw [r16_nat]; simp [rN]
theorem r16_shr (a b : UInt16) : r16 (a >>> b) = r16 a >>> ((r16 b &&& 15#64).toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  have h : (r16 b &&& 15#64).toNat = b.toNat % 2 ^ 4 := by
    rw [BitVec.toNat_and, r16_nat]; exact Nat.and_two_pow_sub_one_eq_mod _ 4
  rw [h, BitVec.toNat_ushiftRight, r16_nat, r16_nat, UInt16.toNat_shiftRight]
  congr 1; omega
theorem r16_shl (a b : UInt16) :
    r16 (a <<< b) = (r16 a <<< ((r16 b &&& 15#64).toNat % 64)) &&& 0xffff#64 := by
  apply BitVec.eq_of_toNat_eq
  have h : (r16 b &&& 15#64).toNat = b.toNat % 2 ^ 4 := by
    rw [BitVec.toNat_and, r16_nat]; exact Nat.and_two_pow_sub_one_eq_mod _ 4
  rw [and_mask16, BitVec.toNat_shiftLeft, h, r16_nat, r16_nat, UInt16.toNat_shiftLeft]
  have : b.toNat % 2 ^ 4 % 64 = b.toNat % 16 := by omega
  rw [this, Nat.mod_mod_of_dvd _ (by decide)]
theorem r16_of8 (a : UInt8) : r16 a.toUInt16 = r8 a := by
  apply BitVec.eq_of_toNat_eq; rw [r16_nat, r8_nat, UInt8.toNat_toUInt16]
theorem r32_of16 (a : UInt16) : r32 a.toUInt32 = r16 a := by
  apply BitVec.eq_of_toNat_eq; rw [r32_nat, r16_nat, UInt16.toNat_toUInt32]
theorem r64_of16 (a : UInt16) : r64 a.toUInt64 = r16 a := by
  apply BitVec.eq_of_toNat_eq; rw [r16_nat]; simp [r64]
theorem r16_of32 (a : UInt32) : r16 a.toUInt16 = r32 a &&& 0xffff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask16, r16_nat, r32_nat, UInt32.toNat_toUInt16]
theorem r8_of16 (a : UInt16) : r8 a.toUInt8 = r16 a &&& 0xff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask8, r8_nat, r16_nat, UInt16.toNat_toUInt8]
theorem r16_ofNat (n : Nat) : r16 n.toUInt16 = rN n &&& 0xffff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask16, r16_nat]; simp [rN]
theorem r16_ofNatU (n : Nat) : r16 (UInt16.ofNat n) = rN n &&& 0xffff#64 := r16_ofNat n
theorem r16_lit (n : Nat) : r16 (no_index (OfNat.ofNat n)) = BitVec.ofNat 64 (n % 65536) := by
  apply BitVec.eq_of_toNat_eq; rw [r16_nat]; simp [OfNat.ofNat, UInt16.toNat_ofNat']
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt n (by decide)) (by decide))).symm

theorem r8_shr (a b : UInt8) : r8 (a >>> b) = r8 a >>> ((r8 b &&& 7#64).toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  have h : (r8 b &&& 7#64).toNat = b.toNat % 2 ^ 3 := by
    rw [BitVec.toNat_and, r8_nat]; exact Nat.and_two_pow_sub_one_eq_mod _ 3
  rw [h, BitVec.toNat_ushiftRight, r8_nat, r8_nat, UInt8.toNat_shiftRight]
  congr 1; omega

/-! ## `Except` / `Option` results as components -/

/-- the tag of an `Except` value: `true` = `ok` (byte `1`, the `inr` of `Spec/Ty.lean`'s sum format) -/
def excTag {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false
/-- a component of the `ok` payload, `z` on `error` -/
def excGet {ε α β : Type} (π : α → β) (z : β) : Except ε α → β
  | .ok a => π a
  | .error _ => z
/-- a component of the `some` payload, `z` on `none` -/
def optGet {α β : Type} (π : α → β) (z : β) : Option α → β
  | some a => π a
  | none => z

@[simp] theorem excTag_ok {ε α : Type} (a : α) : excTag (Except.ok a : Except ε α) = true := rfl
@[simp] theorem excTag_error {ε α : Type} (e : ε) : excTag (Except.error e : Except ε α) = false := rfl
@[simp] theorem excGet_ok {ε α β : Type} (π : α → β) (z : β) (a : α) : excGet π z (Except.ok a : Except ε α) = π a := rfl
@[simp] theorem excGet_error {ε α β : Type} (π : α → β) (z : β) (e : ε) :
    excGet π z (Except.error e : Except ε α) = z := rfl
@[simp] theorem optGet_some {α β : Type} (π : α → β) (z : β) (a : α) : optGet π z (some a) = π a := rfl
@[simp] theorem optGet_none {α β : Type} (π : α → β) (z : β) : optGet π z (none : Option α) = z := rfl

/-! ## `do` in `Except` / `Option`: `bind` pushed into the branches (the normalised equations) -/
theorem exc_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl
theorem exc_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = Except.error e := rfl
theorem exc_bind_ite {ε α β : Type} (c : Prop) [Decidable c] (a b : Except ε α) (f : α → Except ε β) :
    (ite c a b >>= f) = ite c (a >>= f) (b >>= f) := by split <;> rfl
theorem exc_bind_dite {ε α β : Type} (c : Prop) [Decidable c] (a : c → Except ε α) (b : ¬c → Except ε α)
    (f : α → Except ε β) : (dite c a b >>= f) = dite c (fun h => a h >>= f) (fun h => b h >>= f) := by split <;> rfl
theorem exc_pure {ε α : Type} (a : α) : (pure a : Except ε α) = Except.ok a := rfl
theorem exc_throw {ε α : Type} (e : ε) : (throw e : Except ε α) = Except.error e := rfl
theorem opt_bind_some {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl
theorem opt_bind_none {α β : Type} (f : α → Option β) : ((none : Option α) >>= f) = none := rfl
theorem opt_bind_ite {α β : Type} (c : Prop) [Decidable c] (a b : Option α) (f : α → Option β) :
    (ite c a b >>= f) = ite c (a >>= f) (b >>= f) := by split <;> rfl
theorem opt_bind_dite {α β : Type} (c : Prop) [Decidable c] (a : c → Option α) (b : ¬c → Option α)
    (f : α → Option β) : (dite c a b >>= f) = dite c (fun h => a h >>= f) (fun h => b h >>= f) := by split <;> rfl
theorem opt_pure {α : Type} (a : α) : (pure a : Option α) = some a := rfl

end Proven.Frontx
