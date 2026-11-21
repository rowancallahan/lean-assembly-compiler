/- `JArmBits`, the simple L4 group: the sign / register tests and the A64 word encoders of Nano/Codegen/JArm.lean
(`C.e14`, `e42`, `e38`, `e41`, `e50` … `e53`, `e58`, `e62`, `e63`) against `ArmEnc`'s `Nat` encoders.
One theorem `jab_<field>` per field of `JT.JArmBits` (Nano/Run/JArmView.lean), with the field's exact statement. -/
import Nano.Run.JArmView
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

/-! ## toolkit -/

private theorem tN {r : Nat} (h : r < 2 ^ 64) : r.toUInt64.toNat = r := CallProbe.toU_toNat _ h

/-- an OR into a zero bit range `[k, j)` of `a` is a sum -/
private theorem orMid (k j : Nat) {a b : Nat} (H L : Nat) (ha : a = H * 2 ^ j + L) (hL : L < 2 ^ k)
    (hb : b % 2 ^ k = 0) (hbL : b + L < 2 ^ j) : a ||| b = a + b := by
  subst ha
  have hLj : L < 2 ^ j := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hbL
  have e : H * 2 ^ j + L = H * 2 ^ j ||| L := (ArmRA.orA j (Nat.mul_mod_left _ _) hLj).symm
  calc (H * 2 ^ j + L) ||| b = H * 2 ^ j ||| (b ||| L) := by rw [e, Nat.or_assoc, Nat.or_comm L b]
    _ = H * 2 ^ j + (b + L) := by rw [ArmRA.orA k hb hL, ArmRA.orA j (Nat.mul_mod_left _ _) hbL]
    _ = H * 2 ^ j + L + b := by omega

private theorem and511 (n : Nat) : n &&& 511 = n % 512 := Bridge.mask n 9
private theorem iu_mod9 (z : Int) : (iu z).toNat % 512 = mo z 9 := by
  rw [CallProbe.iu_toNat]; unfold mo; omega
private theorem mo_lt9 (z : Int) : mo z 9 < 512 := by unfold mo; omega
private theorem mo_lt19 (z : Int) : mo z 19 < 524288 := by unfold mo; omega
private theorem mo_lt26 (z : Int) : mo z 26 < 67108864 := by unfold mo; omega

/-! ## sign / register tests -/

theorem jab_l4_neg : ∀ z : Int, -2 ^ 63 ≤ z → z < 2 ^ 63 → e14 (iu z) = if z < 0 then 1 else 0 := by
  intro z h1 h2
  unfold e14
  have e := CallProbe.iu_toNat z
  by_cases hz : z < 0
  · rw [if_pos hz, if_pos (by rw [UInt64.lt_iff_toNat_lt, e]; simp; omega)]
  · rw [if_neg hz, if_neg (by rw [UInt64.lt_iff_toNat_lt, e]; simp; omega)]

theorem jab_l4_reg : ∀ r : Nat, mapped r = true → e42 r.toUInt64 = (armReg r).toUInt64 := by
  intro r hm
  rcases ArmRA.mapped_cases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem jab_l4_mapped : ∀ r : Nat, r < 32 → e38 r.toUInt64 = if mapped r = true then 1 else 0 := by
  intro r hr
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨
    r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 25 ∨
    r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem jab_l4_al : ∀ off : Int, -2048 ≤ off → off < 2048 →
    e41 (iu off) = if 0 ≤ off → off % 8 = 0 then 1 else 0 := by
  intro off h1 h2
  unfold e41
  rw [jab_l4_neg off (by omega) (by omega)]
  by_cases hz : off < 0
  · rw [if_pos hz, if_pos (fun h => by omega)]; rfl
  · rw [if_neg hz]
    simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false, e60]
    rw [show e_3 = 7 from rfl, ArmRA.iu_and7 h1 h2]
    by_cases h8 : off % 8 = 0
    · rw [if_pos (by simpa using h8), if_pos (fun _ => h8)]
    · rw [if_neg (by simpa using h8), if_neg (by intro h; exact h8 (h (by omega)))]

/-! ## the word encoders -/

theorem jab_l4_e50 : ∀ cN d n v : Nat, cN < 2 ^ 32 → cN % 2 ^ 22 = 0 → d < 32 → n < 32 → v < 4096 →
    e50 cN.toUInt64 d.toUInt64 n.toUInt64 v.toUInt64 = (cN + v * 2 ^ 10 + n * 2 ^ 5 + d).toUInt64 := by
  intro cN d n v hc hc2 hd hn hv
  unfold e50; apply ArmRA.u64; rw [tN (by omega)]; wnorm
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum

theorem jab_l4_br : ∀ n : Nat, n < 32 → e50 3592355840 0 n.toUInt64 0 = (ArmEnc.brR n).toUInt64 := by
  intro n hn
  have h : e50 3592355840 0 n.toUInt64 0 = (3592355840 : UInt64) ||| (n.toUInt64 <<< 5) := by unfold e50; simp
  rw [h]; unfold brR; apply ArmRA.u64; rw [tN (by omega)]; wnorm
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum

theorem jab_l4_e51 : ∀ cN d n m : Nat, cN < 2 ^ 32 → cN % 2 ^ 10 = 0 → cN / 2 ^ 16 % 32 = 0 → d < 32 → n < 32 →
    m < 32 → e51 cN.toUInt64 d.toUInt64 n.toUInt64 m.toUInt64 = (ArmEnc.rr cN d n m).toUInt64 := by
  intro cN d n m hc hc2 hc3 hd hn hm
  unfold e51 rr; apply ArmRA.u64; rw [tN (by omega)]; wnorm
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  rw [orMid 16 21 (a := cN) (b := m * 65536) (cN / 2097152) (cN % 65536) (by omega) (by omega) (by omega) (by omega)]
  orsum

theorem jab_l4_lsl : ∀ d n sh : Nat, d < 32 → n < 32 → 0 < sh → sh < 64 →
    e50 3544186880 d.toUInt64 n.toUInt64 (63 - sh.toUInt64) ||| (((64 - sh.toUInt64) &&& e_4) <<< 16)
      = (ArmEnc.lslI d n sh).toUInt64 := by
  intro d n sh hd hn h0 hs
  have hv : (63 : UInt64) - sh.toUInt64 = (63 - sh).toUInt64 := by
    apply ArmRA.u64; rw [UInt64.toNat_sub, tN (by omega), tN (by omega)]; simp; omega
  have hm : ((64 : UInt64) - sh.toUInt64) &&& e_4 = ((64 - sh) % 64).toUInt64 := by
    apply ArmRA.u64
    rw [show e_4 = 63 from rfl, UInt64.toNat_and, UInt64.toNat_sub, tN (by omega), tN (by omega)]
    simp only [UInt64.reduceToNat, Bridge.land63]; omega
  rw [hv, hm]
  have h := jab_l4_e50 3544186880 d n (63 - sh) (by omega) (by omega) hd hn (by omega)
  rw [show (3544186880 : UInt64) = (3544186880 : Nat).toUInt64 from rfl, h]
  apply ArmRA.u64; unfold lslI
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, tN (by omega), tN (by omega), tN (by omega)]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [orMid 16 22 (b := (64 - sh) % 64 * 65536) 845 ((63 - sh) * 1024 + n * 32 + d) (by omega) (by omega) (by omega)
    (by omega)]
  omega

theorem jab_l4_alu : ∀ p : Nat, p < 2 ^ 64 → e58 p.toUInt64 = (aluC p).toUInt64 := by
  intro p hp
  by_cases h1 : p = 1; · subst h1; rfl
  by_cases h2 : p = 2; · subst h2; rfl
  by_cases h3 : p = 3; · subst h3; rfl
  by_cases h4 : p = 4; · subst h4; rfl
  by_cases h5 : p = 5; · subst h5; rfl
  by_cases h6 : p = 6; · subst h6; rfl
  by_cases h7 : p = 7; · subst h7; rfl
  have hk : ∀ k : Nat, k < 2 ^ 64 → p ≠ k → (p.toUInt64 == k.toUInt64) = false := fun k hk h => by
    rw [ArmRA.beq_u k hp hk]; simpa using h
  have ha : aluC p = 0xCA000000 := by unfold aluC; split <;> first | rfl | omega
  rw [ha]; unfold e58
  have e1 := hk 1 (by omega) h1; have e2 := hk 2 (by omega) h2; have e3 := hk 3 (by omega) h3
  have e4 := hk 4 (by omega) h4; have e5 := hk 5 (by omega) h5; have e6 := hk 6 (by omega) h6
  have e7 := hk 7 (by omega) h7
  rw [if_neg (by rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, e1]; decide),
    if_neg (by rw [show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, e2]; decide),
    if_neg (by rw [show (3 : UInt64) = (3 : Nat).toUInt64 from rfl, e3]; decide),
    if_neg (by rw [show (4 : UInt64) = (4 : Nat).toUInt64 from rfl, e4]; decide),
    if_neg (by rw [show (5 : UInt64) = (5 : Nat).toUInt64 from rfl, e5]; decide),
    if_neg (by rw [show (6 : UInt64) = (6 : Nat).toUInt64 from rfl, e6]; decide),
    if_neg (by rw [show (7 : UInt64) = (7 : Nat).toUInt64 from rfl, e7]; decide)]
  rfl

theorem jab_l4_e52 : ∀ cN d v j : Nat, cN < 2 ^ 32 → cN % 2 ^ 23 = 0 → d < 32 → v < 65536 → j < 4 →
    e52 cN.toUInt64 d.toUInt64 v.toUInt64 j.toUInt64 = (cN + j * 2 ^ 21 + v * 2 ^ 5 + d).toUInt64 := by
  intro cN d v j hc hc2 hd hv hj
  unfold e52; apply ArmRA.u64; rw [tN (by omega)]; wnorm
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum

theorem jab_l4_e53 : ∀ (cN : Nat) (δ : Int), cN < 2 ^ 32 → cN / 32 % 2 ^ 19 = 0 →
    e53 cN.toUInt64 (iu δ) = (cN + mo δ 19 * 2 ^ 5).toUInt64 := by
  intro cN δ hc hc2
  have := mo_lt19 δ
  unfold e53; apply ArmRA.u64; rw [tN (by omega), show e_9 = 524287 from rfl]; wnorm; rw [ArmRA.iu_mod19]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  rw [orMid 5 24 (a := cN) (b := mo δ 19 * 32) (cN / 16777216) (cN % 32) (by omega) (by omega) (by omega) (by omega)]

theorem jab_l4_cb : ∀ (cN r : Nat) (δ : Int), cN < 2 ^ 32 → cN % 2 ^ 24 = 0 → r < 32 →
    e53 cN.toUInt64 (iu δ) ||| r.toUInt64 = (cN + mo δ 19 * 2 ^ 5 + r).toUInt64 := by
  intro cN r δ hc hc2 hr
  have := mo_lt19 δ
  rw [jab_l4_e53 cN δ hc (by omega)]
  apply ArmRA.u64; rw [UInt64.toNat_or, tN (by omega), tN (by omega), tN (by omega)]
  rw [ArmRA.orA 5 (by omega) (by omega)]

theorem jab_l4_e63 : ∀ (cN : Nat) (δ : Int), cN < 2 ^ 32 → cN % 2 ^ 26 = 0 →
    e63 cN.toUInt64 (iu δ) = (cN + mo δ 26).toUInt64 := by
  intro cN δ hc hc2
  have := mo_lt26 δ
  unfold e63; apply ArmRA.u64; rw [tN (by omega), show e_10 = 67108863 from rfl]; wnorm; rw [ArmRA.iu_mod26]
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum

theorem jab_l4_e62 : ∀ (cN t n : Nat) (f : Int), cN < 2 ^ 32 → cN % 2 ^ 21 = 0 → t < 32 → n < 32 →
    e62 cN.toUInt64 t.toUInt64 n.toUInt64 (iu f) = (cN + mo f 9 * 2 ^ 12 + n * 2 ^ 5 + t).toUInt64 := by
  intro cN t n f hc hc2 ht hn
  have := mo_lt9 f
  unfold e62; apply ArmRA.u64; rw [tN (by omega), show e_8 = 511 from rfl]; wnorm
  simp only [and511]; rw [iu_mod9]
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum

end JT
