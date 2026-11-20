/- Model-independent facts about rv2arm's Nat-built words (`ArmEnc.*`): opcode masks (`mask32`), fields (`fldt`,
`immt`), branch offsets (`off19`, `off26`, Sail's `sign_extend (imm ++ 00)` = `sx2`) and the four conditions after
`subs` (`cond_sub`). Copied from `Arm/apc` (`Blocks/Enc`, `Apc/Sym`, `Blocks/A64DM`, `Blocks/KBr`, `BridgeBr.sx2`),
where they are proved for the DeepMind surrogate; none of them mentions a model, so importing them would only drag
in the DeepMind package. -/
import Nano.V2Self.Proof.Machine.A64Sem
import Arm.Small
open Sail
namespace ArmSail
open ArmProof

abbrev wd (n : Nat) : BitVec 32 := BitVec.ofNat 32 n

theorem fin32 : ∀ j < 32, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
    j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨
    j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by intro j hj; omega

set_option hygiene false in
/-- `wd n &&& K = C` for `n` = literal opcode + bounded fields: bit by bit, each by `omega` -/
macro "mask32" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  rcases fin32 j hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp <;> omega))

/-- Sail's `slice` is `extractLsb'` -/
theorem sl (w : BitVec 32) (i k : Nat) : Sail.BitVec.slice w i k = w.extractLsb' i k := rfl

/-- a field of `wd n`, as a number -/
theorem fld (n i k : Nat) : (Sail.BitVec.slice (wd n) i k).toNat = n % 2 ^ 32 / 2 ^ i % 2 ^ k := by
  simp [sl, Nat.shiftRight_eq_div_pow]

/-- a field equation `(slice (wd n) i k).toNat = v` -/
macro "fldt" : tactic => `(tactic| (rw [fld]; omega))
-- `rw`, not `simp`: the `simp` proof of `movk`'s immediate made the kernel check recurse too deep
/-- an immediate equation `(slice (wd n) i k).setWidth 64 = BitVec.ofNat 64 v` -/
macro "immt" : tactic => `(tactic| (apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, fld, BitVec.toNat_ofNat]; omega))

theorem mo_lt (f : Int) (k : Nat) : ArmEnc.mo f k < 2 ^ k := by
  unfold ArmEnc.mo
  have hp := Nat.pow_pos (n := k) (by decide : 0 < 2)
  have h1 := Int.emod_lt_of_pos f (show (0 : Int) < ((2 ^ k : Nat) : Int) by omega)
  have h2 := Int.emod_nonneg f (show ((2 ^ k : Nat) : Int) ≠ 0 by omega)
  omega

theorem sx2 {n : Nat} (x : BitVec n) (h : n + 2 ≤ 64) : sign_extend (x +++ 0#2) 64 = (x.signExtend 64) <<< 2 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.msb_append]
  by_cases h1 : i < 2
  · simp [h1]; intros; omega
  · simp [h1, hi]
    have h3 : i - 2 < 64 := by omega
    simp only [h3, decide_true, Bool.true_and]
    by_cases h2 : i < n + 2
    · simp [h2, show i - 2 < n by omega]
    · simp only [h2, show ¬ i - 2 < n by omega, if_false]
      by_cases hn : n = 0
      · subst hn; simp [BitVec.msb, BitVec.getMsbD]
      · simp [hn]

theorem off_fwd {w : Nat} (hw : 1 ≤ w) (hw' : w ≤ 64) {n : Nat} (hn : n < 2 ^ (w - 1)) :
    ((BitVec.ofNat w n).signExtend 64) <<< 2 = BitVec.ofNat 64 (4 * n) := by
  have h2 : 2 ^ (w - 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ w by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  simp only [show ¬ 2 ^ (w - 1) ≤ n by omega, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    Nat.shiftLeft_eq]
  omega

theorem off_back {w : Nat} (hw : 1 ≤ w) (hw' : w ≤ 62) {n : Nat} (hn : 0 < n) (hn' : n ≤ 2 ^ (w - 1)) :
    ((BitVec.ofNat w (2 ^ w - n)).signExtend 64) <<< 2 = BitVec.ofNat 64 (2 ^ 64 - 4 * n) := by
  have h2 : 2 ^ (w - 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have h4 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2 ^ w - n < 2 ^ w by omega), Nat.mod_eq_of_lt (show 2 ^ w - n < 2 ^ 64 by omega)]
  simp only [show 2 ^ (w - 1) ≤ 2 ^ w - n by omega, decide_true, ↓reduceIte, Nat.shiftLeft_eq]
  generalize 2 ^ w = P at *; generalize 2 ^ (w - 1) = Q at *
  omega

theorem ofInt_toNat (f : Int) : (UInt64.ofInt f).toNat = (f % 2 ^ 64).toNat := by
  unfold UInt64.ofInt
  rw [UInt64.toNat_ofNat']
  have h0 := Int.emod_nonneg f (show (2 ^ 64 : Int) ≠ 0 by decide)
  have h1 := Int.emod_lt_of_pos f (show (0 : Int) < 2 ^ 64 by decide)
  omega

/-- the branch offset field, as `A64Sem` writes it -/
theorem offW (w : Nat) (hw1 : 2 ≤ w) (hw2 : w ≤ 26) (f : Int) (hm : ArmEnc.mo f w = if 0 ≤ f then f.toNat else 2 ^ w - f.natAbs)
    (h1 : -2 ^ (w - 1) ≤ f) (h2 : f < 2 ^ (w - 1)) :
    (BitVec.ofNat w (ArmEnc.mo f w)).signExtend 64 <<< 2 = (4 * UInt64.ofInt f).toBitVec := by
  have p1 : (2 : Int) ^ (w - 1) = ((2 ^ (w - 1) : Nat) : Int) := by push_cast; rfl
  have p2 : 2 ^ (w - 1) ≤ 2 ^ 25 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [hm]; split
  · rename_i h0
    rw [off_fwd (w := w) (by omega) (by omega) (show f.toNat < 2 ^ (w - 1) by omega)]
    apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_mul, ofInt_toNat]; omega
  · rename_i h0
    have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    rw [off_back (w := w) (by omega) (by omega) (show 0 < f.natAbs by omega) (show f.natAbs ≤ 2 ^ (w - 1) by omega)]
    apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_mul, ofInt_toNat]; omega

theorem off19 (f : Int) (h1 : -2 ^ 18 ≤ f) (h2 : f < 2 ^ 18) :
    (BitVec.ofNat 19 (ArmEnc.mo f 19)).signExtend 64 <<< 2 = (4 * UInt64.ofInt f).toBitVec :=
  offW 19 (by decide) (by decide) f (by unfold ArmEnc.mo; split <;> simp only [Nat.reducePow] <;> omega) h1 h2
theorem off26 (f : Int) (h1 : -2 ^ 25 ≤ f) (h2 : f < 2 ^ 25) :
    (BitVec.ofNat 26 (ArmEnc.mo f 26)).signExtend 64 <<< 2 = (4 * UInt64.ofInt f).toBitVec :=
  offW 26 (by decide) (by decide) f (by unfold ArmEnc.mo; split <;> simp only [Nat.reducePow] <;> omega) h1 h2

/-- the conditions EQ/NE/HS/LO after `subs x16, xn, xm` -/
theorem cond_sub (A : AState) (c : Nat) (hc : c < 4) (x y : UInt64) (v : BitVec 64) :
    ((A.setSub x.toBitVec y.toBitVec).setX 16 v).cond (BitVec.ofNat 4 c) = JT.condV c x y := by
  have hxy : (x.toBitVec - y.toBitVec = 0#64) ↔ x = y := by
    constructor
    · intro h; apply UInt64.toBitVec_inj.mp
      rw [← BitVec.sub_add_cancel x.toBitVec y.toBitVec, h, BitVec.zero_add]
    · intro h; rw [h, BitVec.sub_self]
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp [AState.cond, AState.setX, AState.setSub, JT.condV, hxy, UInt64.lt_iff_toNat_lt]
  · by_cases e : x = y <;> simp [e]
  · by_cases e : x = y <;> simp [e]
  · by_cases e : y.toNat ≤ x.toNat <;> simp [e] <;> omega

end ArmSail
