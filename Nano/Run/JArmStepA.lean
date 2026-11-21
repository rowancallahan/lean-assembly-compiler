/- `StepAt` lemmas, group A (see JArmStep.lean). -/
import Nano.Run.JArmStep
import Nano.Run.JArmInst
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

/-! ## helpers (private: the sibling files have their own) -/

private theorem tU_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a.toUInt64 = b.toUInt64) : a = b := by
  have := congrArg UInt64.toNat h
  rwa [ArmRA.toU_toNat ha, ArmRA.toU_toNat hb] at this

private theorem aR_lt (r : Nat) : armReg r < 32 := by unfold armReg; split <;> omega

private theorem mul_ne {a b : UInt64} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 := by
  constructor <;> (intro e; subst e; simp at h)

private theorem ite_ne {p : Prop} [Decidable p] (h : (if p then (1 : UInt64) else 0) ≠ 0) : p := by
  by_cases hp : p
  · exact hp
  · rw [if_neg hp] at h; exact absurd rfl h

private theorem mr_mapped {r : Nat} (h : NTm.mr r = true) : mapped r = true ∧ r ≠ 0 := by
  unfold NTm.mr at h
  have := Bool.and_eq_true_iff.1 h
  exact ⟨this.1, of_decide_eq_true this.2⟩

/-- the translator's `mr` test -/
private theorem e39_mr (B : JArmBits) (r : Nat) (hr : r < 32) :
    e39 r.toUInt64 = if NTm.mr r = true then 1 else 0 := by
  unfold e39 NTm.mr
  rw [B.l4_mapped r hr]
  by_cases h0 : r = 0
  · subst h0; rfl
  · rw [ArmRA.beq0 (by omega)]
    simp [h0]

private theorem e39_ne (B : JArmBits) {r : Nat} (hr : r < 32) (h : e39 r.toUInt64 ≠ 0) : NTm.mr r = true := by
  rw [e39_mr B r hr] at h; exact ite_ne h

private theorem e38_ne (B : JArmBits) {r : Nat} (hr : r < 32) (h : e38 r.toUInt64 ≠ 0) : mapped r = true := by
  rw [B.l4_mapped r hr] at h; exact ite_ne h

/-- the J instruction at pc `q` and the translator's accessors on it -/
private theorem setup (B : JArmBits) {Cj : List J} (hJ : ∀ j ∈ Cj, JOK j) (hl : Cj.length < 2 ^ 18) (q : Nat)
    (hq : q < Cj.length) :
    ∃ j r, Cj.drop q = j :: r ∧ JOK j ∧ e21 (Cj.map encG) q.toUInt64 = jA j ∧ e22 (Cj.map encG) q.toUInt64 = jB j ∧
      e23 (Cj.map encG) q.toUInt64 = jC j ∧ e24 (Cj.map encG) q.toUInt64 = jop j := by
  refine ⟨Cj[q], Cj.drop (q + 1), List.drop_eq_getElem_cons hq, hJ _ (List.getElem_mem hq), ?_, ?_, ?_, ?_⟩
  · rw [acc21 B hJ hl q (by omega)]; unfold fA; rw [List.getElem?_eq_getElem hq]; rfl
  · rw [acc22 B hJ hl q (by omega)]; unfold fB; rw [List.getElem?_eq_getElem hq]; rfl
  · rw [acc23 B hJ hl q (by omega)]; unfold fC; rw [List.getElem?_eq_getElem hq]; rfl
  · rw [acc24 B hJ hl q (by omega)]; unfold fO; rw [List.getElem?_eq_getElem hq]; rfl

private theorem memW_len (st : Bool) (t n : Nat) (off : Int) : (NTm.memW st t n off).length ≤ 2 := by
  unfold NTm.memW
  split
  · simp
  · split <;> simp

private theorem aluC_ok (op : Nat) : aluC op < 2 ^ 32 ∧ aluC op % 2 ^ 10 = 0 ∧ aluC op / 2 ^ 16 % 32 = 0 := by
  unfold aluC; split <;> refine ⟨by omega, by omega, by omega⟩

private theorem e66_iu (B : JArmBits) (z : Int) (h1 : -2 ^ 63 ≤ z) (h2 : z < 2 ^ 63) :
    e66 (iu z) = z.toNat.toUInt64 := by
  unfold e66
  rw [B.l4_neg z h1 h2]
  by_cases h : z < 0
  · rw [if_pos h]
    have : z.toNat = 0 := by omega
    rw [this]; rfl
  · rw [if_neg h]
    exact ArmRA.iu_nn (by omega) h2

/-! ## the kind of the head instruction, from the atom code -/

private theorem ite_imp {c : Prop} [Decidable c] {a b t : UInt64} {P : Prop} (ha : c → a = t → P)
    (hb : ¬c → b = t → P) : (if c then a else b) = t → P := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

private theorem ck2 (l : List J) : candC l = 2 → kd l 0 = 1 := by
  unfold candC; simp only []
  repeat' (apply ite_imp <;> intro _)
  all_goals (intro h; first | exact absurd h (by decide) | exact eq_of_beq (by assumption))
private theorem ck3 (l : List J) : candC l = 3 → kd l 0 = 8 := by
  unfold candC; simp only []
  repeat' (apply ite_imp <;> intro _)
  all_goals (intro h; first | exact absurd h (by decide) | exact eq_of_beq (by assumption))
private theorem ck4 (l : List J) : candC l = 4 → kd l 0 = 4 := by
  unfold candC; simp only []
  repeat' (apply ite_imp <;> intro _)
  all_goals (intro h; first | exact absurd h (by decide) | exact eq_of_beq (by assumption))
private theorem ck5 (l : List J) : candC l = 5 → kd l 0 = 5 := by
  unfold candC; simp only []
  repeat' (apply ite_imp <;> intro _)
  all_goals (intro h; first | exact absurd h (by decide) | exact eq_of_beq (by assumption))
private theorem ck16 (l : List J) : candC l = 16 → kd l 0 = 2 := by
  unfold candC; simp only []
  repeat' (apply ite_imp <;> intro _)
  all_goals (intro h; first | exact absurd h (by decide) | exact eq_of_beq (by assumption))
private theorem ck20 (l : List J) : candC l = 20 → kd l 0 = 13 := by
  unfold candC; simp only []
  repeat' (apply ite_imp <;> intro _)
  all_goals (intro h; first | exact absurd h (by decide) | exact eq_of_beq (by assumption))
private theorem ck21 (l : List J) : candC l = 21 → kd l 0 = 14 := by
  unfold candC; simp only []
  repeat' (apply ite_imp <;> intro _)
  all_goals (intro h; first | exact absurd h (by decide) | exact eq_of_beq (by assumption))
private theorem ck22 (l : List J) : candC l = 22 → kd l 0 = 6 ∧ fC l 0 = 0 := by
  unfold candC; simp only []
  repeat' (apply ite_imp <;> intro _)
  all_goals (intro h; first | exact absurd h (by decide) | exact ⟨eq_of_beq (by assumption), eq_of_beq (by assumption)⟩)

/-! ## the translator's functions at a fixed atom code -/

private theorem e37_2 (c : Buf) (n i : UInt64) : e37 c n i 2 = e39 (e21 c i) * e38 (e22 c i) := rfl
private theorem e37_3 (c : Buf) (n i : UInt64) : e37 c n i 3 = e39 (e21 c i) * e39 (e22 c i) * e39 (e23 c i) := rfl
private theorem e37_4 (c : Buf) (n i : UInt64) : e37 c n i 4 = e39 (e21 c i) * e39 (e22 c i) * e41 (e23 c i) := rfl
private theorem e37_5 (c : Buf) (n i : UInt64) : e37 c n i 5 = e38 (e21 c i) * e39 (e22 c i) * e41 (e23 c i) := rfl
private theorem e37_16 (c : Buf) (n i : UInt64) : e37 c n i 16 =
    e39 (e21 c i) * e39 (e22 c i) * (if e23 c i == 0 then 0 else if e23 c i < 64 then 1 else 0) := rfl
private theorem e37_20 (c : Buf) (n i : UInt64) : e37 c n i 20 = if e21 c i < 2 then 1 else 0 := rfl
private theorem e37_21 (c : Buf) (n i : UInt64) : e37 c n i 21 = if e22 c i == 1 then 1 else e60 (e22 c i) 14 := rfl
private theorem e37_22 (c : Buf) (n i : UInt64) : e37 c n i 22 = e39 (e21 c i) * e39 (e22 c i) := rfl

private theorem e40_2 (c : Buf) (n : UInt64) (z o : Buf) (i : UInt64) : e40 c n z o i 2 =
    if e22 c i == 0 then e56 o (e42 (e21 c i)) (e23 c i)
    else if e14 (e23 c i) == 1 then bpush o (e50 3506438144 (e42 (e21 c i)) (e42 (e22 c i)) (0 - e23 c i))
    else bpush o (e50 2432696320 (e42 (e21 c i)) (e42 (e22 c i)) (e23 c i)) := rfl
private theorem e40_3 (c : Buf) (n : UInt64) (z o : Buf) (i : UInt64) : e40 c n z o i 3 =
    if e24 c i == 3 then
      bpush (bpush o (e52 3531603968 17 0 0)) (e51 2600485888 (e42 (e21 c i)) (e42 (e22 c i)) (e42 (e23 c i)))
    else bpush o (e51 (e58 (e24 c i)) (e42 (e21 c i)) (e42 (e22 c i)) (e42 (e23 c i))) := rfl
private theorem e40_4 (c : Buf) (n : UInt64) (z o : Buf) (i : UInt64) : e40 c n z o i 4 =
    e57 o 0 (e42 (e21 c i)) (e42 (e22 c i)) (e23 c i) := rfl
private theorem e40_5 (c : Buf) (n : UInt64) (z o : Buf) (i : UInt64) : e40 c n z o i 5 =
    if e21 c i == 0 then e57 (bpush o (e52 3531603968 17 0 0)) 1 17 (e42 (e22 c i)) (e23 c i)
    else e57 o 1 (e42 (e21 c i)) (e42 (e22 c i)) (e23 c i) := rfl
private theorem e40_16 (c : Buf) (n : UInt64) (z o : Buf) (i : UInt64) : e40 c n z o i 16 =
    bpush o (e50 3544186880 (e42 (e21 c i)) (e42 (e22 c i)) (63 - e23 c i) ||| (((64 - e23 c i) &&& e_4) <<< 16)) :=
  rfl
private theorem e40_20 (c : Buf) (n : UInt64) (z o : Buf) (i : UInt64) : e40 c n z o i 20 =
    bpush o (e63 (if e21 c i == 0 then 335544320 else 2483027968) (e59 z (e65 c n i 20) - bsize o)) := rfl
private theorem e40_21 (c : Buf) (n : UInt64) (z o : Buf) (i : UInt64) : e40 c n z o i 21 =
    bpush o (e50 3592355840 0 (e42 (e22 c i)) 0) := rfl
private theorem e40_22 (c : Buf) (n : UInt64) (z o : Buf) (i : UInt64) : e40 c n z o i 22 =
    bpush o (e50 956301312 (e42 (e21 c i)) (e42 (e22 c i)) 0) := rfl
private theorem e65_20 (c : Buf) (n i : UInt64) : e65 c n i 20 = e66 (i + e23 c i) := rfl

/-! ## 16: slli -/

theorem stepAt_16 : StepAt 16 := by
  intro Cj hJ hl q hq hc he
  have B := jArmBits
  obtain ⟨j, r, hd, hj, a1, a2, a3, a4⟩ := setup B hJ hl q hq
  rw [hd] at hc ⊢
  have k : jk j = 2 := ck16 _ hc
  cases j <;> try (simp [jk] at k; done)
  rename_i d n sh
  obtain ⟨⟨hd', hn', hs'⟩, -⟩ := hj
  simp only [jA, jB, jC] at a1 a2 a3
  rw [e37_16, a1, a2, a3] at he
  obtain ⟨he1, he3⟩ := mul_ne he
  obtain ⟨he1, he2⟩ := mul_ne he1
  have m1 := e39_ne B hd' he1
  have m2 := e39_ne B hn' he2
  have s0 : sh ≠ 0 := by
    intro e; subst e; exact he3 rfl
  refine ⟨.slli d n sh, rfl, rfl, ?_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [NTm.ok, m1, m2, Bool.true_and]
    exact decide_eq_true ⟨by omega, hs'⟩
  · show (1 : Nat) ≤ 4; omega
  · intro p hp; cases hp
  · intro z o
    rw [e40_16, a1, a2, a3, B.l4_reg d (mr_mapped m1).1, B.l4_reg n (mr_mapped m2).1,
      B.l4_lsl (armReg d) (armReg n) sh (aR_lt d) (aR_lt n) (by omega) hs']
    rfl

/-! ## 3: alu -/

theorem stepAt_3 : StepAt 3 := by
  intro Cj hJ hl q hq hc he
  have B := jArmBits
  obtain ⟨j, r, hd, hj, a1, a2, a3, a4⟩ := setup B hJ hl q hq
  rw [hd] at hc ⊢
  have k : jk j = 8 := ck3 _ hc
  cases j <;> try (simp [jk] at k; done)
  rename_i op d x y
  obtain ⟨⟨hd', hx', hy', ho1, ho2⟩, -⟩ := hj
  simp only [jA, jB, jC, jop] at a1 a2 a3 a4
  rw [e37_3, a1, a2, a3] at he
  obtain ⟨he1, he3⟩ := mul_ne he
  obtain ⟨he1, he2⟩ := mul_ne he1
  have m1 := e39_ne B hd' he1
  have m2 := e39_ne B hx' he2
  have m3 := e39_ne B hy' he3
  refine ⟨.alu op d x y, rfl, rfl, ?_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [NTm.ok, m1, m2, m3, Bool.true_and]
  · unfold NTm.alen
    simp only [NTm.a]
    split <;> simp
  · intro p hp; cases hp
  · intro z o
    rw [e40_3, a1, a2, a3, a4, B.l4_reg d (mr_mapped m1).1, B.l4_reg x (mr_mapped m2).1,
      B.l4_reg y (mr_mapped m3).1]
    by_cases h3 : op = 3
    · subst h3
      rw [if_pos (show (Nat.toUInt64 3 == 3) = true from rfl),
        show e52 3531603968 17 0 0 = (ArmEnc.movz 17 0).toUInt64 from
          B.l4_e52 3531603968 17 0 0 (by omega) (by omega) (by omega) (by omega) (by omega),
        show e51 2600485888 (armReg d).toUInt64 (armReg x).toUInt64 (armReg y).toUInt64 = _ from
          B.l4_e51 (aluC 3) (armReg d) (armReg x) (armReg y) (aluC_ok 3).1 (aluC_ok 3).2.1 (aluC_ok 3).2.2
            (aR_lt d) (aR_lt x) (aR_lt y)]
      rw [bpush, bpush, List.append_assoc]
      rfl
    · rw [if_neg (show ¬ (op.toUInt64 == 3) = true from fun h => h3 (tU_inj (by omega) (by omega) (eq_of_beq h))), B.l4_alu op (by omega),
        B.l4_e51 (aluC op) (armReg d) (armReg x) (armReg y) (aluC_ok op).1 (aluC_ok op).2.1 (aluC_ok op).2.2
            (aR_lt d) (aR_lt x) (aR_lt y)]
      simp only [NTm.a, if_neg h3]
      rfl

/-! ## 2: addi -/

private theorem liL_small (t : Nat) (imm : Int) (h1 : -2048 ≤ imm) (h2 : imm < 2048) :
    (liL t (UInt64.ofInt imm).toNat).length ≤ 4 := by
  rw [← iu_ofInt, iu_toNat]
  unfold liL
  by_cases h : 0 ≤ imm
  · rw [if_pos (by omega)]; simp
  · rw [if_neg (by omega), if_pos (by omega)]; simp

theorem stepAt_2 : StepAt 2 := by
  intro Cj hJ hl q hq hc he
  have B := jArmBits
  obtain ⟨j, r, hd, hj, a1, a2, a3, a4⟩ := setup B hJ hl q hq
  rw [hd] at hc ⊢
  have k : jk j = 1 := ck2 _ hc
  cases j <;> try (simp [jk] at k; done)
  rename_i d n imm
  obtain ⟨⟨hd', hn', hi1, hi2⟩, -⟩ := hj
  simp only [jA, jB, jC] at a1 a2 a3
  rw [e37_2, a1, a2] at he
  obtain ⟨he1, he2⟩ := mul_ne he
  have m1 := e39_ne B hd' he1
  have m2 := e38_ne B hn' he2
  refine ⟨.addi d n imm, rfl, rfl, ?_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [NTm.ok, m1, m2, Bool.true_and]
    rw [decide_eq_true (show -4096 < imm ∧ imm < 4096 from ⟨by omega, by omega⟩)]
    exact decide_eq_true (fun _ => ⟨hi1, hi2⟩)
  · unfold NTm.alen
    simp only [NTm.a]
    split
    · exact liL_small _ imm hi1 hi2
    · split <;> simp
  · intro p hp; cases hp
  · intro z o
    rw [e40_2, a1, a2, a3, B.l4_reg d (mr_mapped m1).1]
    by_cases h0 : n = 0
    · subst h0
      rw [if_pos (show (Nat.toUInt64 0 == 0) = true from rfl), B.l4_li o (armReg d) (iu imm) (aR_lt d), iu_ofInt]
      rfl
    · rw [if_neg (show ¬ (n.toUInt64 == 0) = true from fun h => h0 (tU_inj (by omega) (by omega) (eq_of_beq h))),
        B.l4_reg n m2,
        B.l4_neg imm (by omega) (by omega)]
      simp only [NTm.a, if_neg h0]
      by_cases hn : imm < 0
      · have e : 0 - iu imm = imm.natAbs.toUInt64 := by
          apply ArmRA.u64; rw [UInt64.toNat_sub, iu_toNat, ArmRA.toU_toNat (by omega)]; simp; omega
        rw [if_pos hn, if_pos (show ((1 : UInt64) == 1) = true from rfl), if_pos hn, e,
          show e50 3506438144 (armReg d).toUInt64 (armReg n).toUInt64 imm.natAbs.toUInt64 = _ from
            B.l4_e50 3506438144 (armReg d) (armReg n) imm.natAbs (by omega) (by omega) (aR_lt d) (aR_lt n) (by omega)]
        rfl
      · rw [if_neg hn, if_neg (show ¬ ((0 : UInt64) == 1) = true from by decide), if_neg hn, ArmRA.iu_nn (by omega) (by omega),
          show e50 2432696320 (armReg d).toUInt64 (armReg n).toUInt64 imm.toNat.toUInt64 = _ from
            B.l4_e50 2432696320 (armReg d) (armReg n) imm.toNat (by omega) (by omega) (aR_lt d) (aR_lt n) (by omega)]
        rfl

/-! ## 4: ld -/

theorem stepAt_4 : StepAt 4 := by
  intro Cj hJ hl q hq hc he
  have B := jArmBits
  obtain ⟨j, r, hd, hj, a1, a2, a3, a4⟩ := setup B hJ hl q hq
  rw [hd] at hc ⊢
  have k : jk j = 4 := ck4 _ hc
  cases j <;> try (simp [jk] at k; done)
  rename_i d n off
  obtain ⟨⟨hd', hn', hi1, hi2⟩, -⟩ := hj
  simp only [jA, jB, jC] at a1 a2 a3
  rw [e37_4, a1, a2, a3] at he
  obtain ⟨he1, he3⟩ := mul_ne he
  obtain ⟨he1, he2⟩ := mul_ne he1
  have m1 := e39_ne B hd' he1
  have m2 := e39_ne B hn' he2
  rw [B.l4_al off hi1 hi2] at he3
  have hal := ite_ne he3
  refine ⟨.ld d n off, rfl, rfl, ?_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [NTm.ok, m1, m2, Bool.true_and]
    exact decide_eq_true ⟨by omega, by omega, hal⟩
  · exact Nat.le_trans (memW_len _ _ _ _) (by omega)
  · intro p hp; cases hp
  · intro z o
    rw [e40_4, a1, a2, a3, B.l4_reg d (mr_mapped m1).1, B.l4_reg n (mr_mapped m2).1]
    exact B.l4_mem o false (armReg d) (armReg n) off (aR_lt d) (aR_lt n) (by omega) (by omega) hal

/-! ## 5: sd -/

theorem stepAt_5 : StepAt 5 := by
  intro Cj hJ hl q hq hc he
  have B := jArmBits
  obtain ⟨j, r, hd, hj, a1, a2, a3, a4⟩ := setup B hJ hl q hq
  rw [hd] at hc ⊢
  have k : jk j = 5 := ck5 _ hc
  cases j <;> try (simp [jk] at k; done)
  rename_i s n off
  obtain ⟨⟨hd', hn', hi1, hi2⟩, -⟩ := hj
  simp only [jA, jB, jC] at a1 a2 a3
  rw [e37_5, a1, a2, a3] at he
  obtain ⟨he1, he3⟩ := mul_ne he
  obtain ⟨he1, he2⟩ := mul_ne he1
  have m1 := e38_ne B hd' he1
  have m2 := e39_ne B hn' he2
  rw [B.l4_al off hi1 hi2] at he3
  have hal := ite_ne he3
  refine ⟨.sd s n off, rfl, rfl, ?_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [NTm.ok, m1, m2, Bool.true_and]
    exact decide_eq_true ⟨by omega, by omega, hal⟩
  · unfold NTm.alen
    simp only [NTm.a]
    have := memW_len true 17 (armReg n) off
    have := memW_len true (armReg s) (armReg n) off
    split
    · simp only [List.length_cons]; omega
    · omega
  · intro p hp; cases hp
  · intro z o
    rw [e40_5, a1, a2, a3, B.l4_reg n (mr_mapped m2).1]
    by_cases h0 : s = 0
    · subst h0
      rw [if_pos (show (Nat.toUInt64 0 == 0) = true from rfl),
        show e52 3531603968 17 0 0 = (ArmEnc.movz 17 0).toUInt64 from
          B.l4_e52 3531603968 17 0 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
      have e := B.l4_mem (bpush o (ArmEnc.movz 17 0).toUInt64) true 17 (armReg n) off (by omega) (aR_lt n) (by omega)
        (by omega) hal
      refine e.trans ?_
      rw [bpush, List.append_assoc]
      rfl
    · rw [if_neg (show ¬ (s.toUInt64 == 0) = true from fun h => h0 (tU_inj (by omega) (by omega) (eq_of_beq h))),
        B.l4_reg s m1]
      simp only [NTm.a, if_neg h0]
      exact B.l4_mem o true (armReg s) (armReg n) off (aR_lt s) (aR_lt n) (by omega) (by omega) hal

/-! ## 20: jal -/

theorem stepAt_20 : StepAt 20 := by
  intro Cj hJ hl q hq hc he
  have B := jArmBits
  obtain ⟨j, r, hd, hj, a1, a2, a3, a4⟩ := setup B hJ hl q hq
  rw [hd] at hc ⊢
  have k : jk j = 13 := ck20 _ hc
  cases j <;> try (simp [jk] at k; done)
  rename_i rd off
  obtain ⟨hrd, ho⟩ := hj
  obtain ⟨ho1, ho2⟩ := ho rd off rfl
  have hrd : rd < 32 := hrd
  simp only [jA, jB, jC] at a1 a2 a3
  rw [e37_20, a1] at he
  have hlt : rd < 2 := (tU_lt (by omega) (by omega)).1 (ite_ne he)
  have e65' : e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 20 = (NTm.jt q off).toUInt64 := by
    have e : q.toUInt64 + iu off = iu ((q : Int) + off) := by
      apply ArmRA.u64; rw [UInt64.toNat_add, iu_toNat, iu_toNat, ArmRA.toU_toNat (by omega)]; omega
    rw [e65_20, a3, e, e66_iu B _ (by omega) (by omega)]
    rfl
  refine ⟨.jal rd off, rfl, rfl, ?_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · exact decide_eq_true (show rd = 0 ∨ rd = 1 by omega)
  · show (1 : Nat) ≤ 4; omega
  · intro p hp
    have hp' : p = NTm.jt q off := by simpa [NTm.tg] using hp
    subst hp'
    refine ⟨?_, e65'⟩
    unfold NTm.jt; omega
  · intro z o
    have eg : e59 z (NTm.jt q off).toUInt64 - bsize o = iu ((zpi z (NTm.jt q off) : Int) - (o.length : Int)) := by
      apply ArmRA.u64
      have hb : (bsize o).toNat = o.length % 2 ^ 64 := by
        show (UInt64.ofNat o.length).toNat = _
        rw [UInt64.toNat_ofNat']
      have := (e59 z (NTm.jt q off).toUInt64).toNat_lt
      rw [UInt64.toNat_sub, iu_toNat, hb]
      unfold zpi
      omega
    rw [e40_20, a1, e65', eg]
    by_cases h0 : rd = 0
    · subst h0
      rw [if_pos (show (Nat.toUInt64 0 == 0) = true from rfl), show e63 335544320 _ = _ from B.l4_e63 335544320 _ (by omega) (by omega)]
      rfl
    · have h1 : rd = 1 := by omega
      subst h1
      rw [if_neg (show ¬ (Nat.toUInt64 1 == 0) = true from by decide), show e63 2483027968 _ = _ from B.l4_e63 2483027968 _ (by omega) (by omega)]
      rfl

/-! ## 21: jalr -/

theorem stepAt_21 : StepAt 21 := by
  intro Cj hJ hl q hq hc he
  have B := jArmBits
  obtain ⟨j, r, hd, hj, a1, a2, a3, a4⟩ := setup B hJ hl q hq
  rw [hd] at hc ⊢
  have k : jk j = 14 := ck21 _ hc
  cases j <;> try (simp [jk] at k; done)
  rename_i rd rs
  obtain ⟨⟨hrd, hrs⟩, -⟩ := hj
  subst hrd
  simp only [jA, jB, jC] at a1 a2 a3
  rw [e37_21, a2] at he
  have hr : rs = 1 ∨ rs = 14 := by
    by_cases h1 : (rs.toUInt64 == 1) = true
    · exact Or.inl (tU_inj (by omega) (by omega) (eq_of_beq h1))
    · rw [if_neg h1] at he
      unfold e60 at he
      exact Or.inr (tU_inj (by omega) (by omega) (eq_of_beq (ite_ne he)))
  have hm : mapped rs = true := by rcases hr with rfl | rfl <;> rfl
  refine ⟨.jalr rs, rfl, rfl, ?_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · exact decide_eq_true hr
  · show (1 : Nat) ≤ 4; omega
  · intro p hp; cases hp
  · intro z o
    rw [e40_21, a2, B.l4_reg rs hm, B.l4_br (armReg rs) (aR_lt rs)]
    rfl

/-! ## 22: sb -/

theorem stepAt_22 : StepAt 22 := by
  intro Cj hJ hl q hq hc he
  have B := jArmBits
  obtain ⟨j, r, hd, hj, a1, a2, a3, a4⟩ := setup B hJ hl q hq
  rw [hd] at hc ⊢
  obtain ⟨k, kc⟩ := ck22 _ hc
  replace k : jk j = 6 := k
  replace kc : jC j = 0 := kc
  cases j <;> try (simp [jk] at k; done)
  rename_i s n off
  obtain ⟨⟨hs', hn', hi1, hi2⟩, -⟩ := hj
  simp only [jA, jB, jC] at a1 a2 a3 kc
  have h0 : off = 0 := by
    have := congrArg UInt64.toNat kc
    rw [iu_toNat] at this
    change _ = 0 at this
    omega
  subst h0
  rw [e37_22, a1, a2] at he
  obtain ⟨he1, he2⟩ := mul_ne he
  have m1 := e39_ne B hs' he1
  have m2 := e39_ne B hn' he2
  refine ⟨.sb s n, rfl, rfl, ?_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [NTm.ok, m1, m2, Bool.true_and]
  · show (1 : Nat) ≤ 4; omega
  · intro p hp; cases hp
  · intro z o
    rw [e40_22, a1, a2, B.l4_reg s (mr_mapped m1).1, B.l4_reg n (mr_mapped m2).1,
      show e50 956301312 (armReg s).toUInt64 (armReg n).toUInt64 0 = _ from
        B.l4_e50 956301312 (armReg s) (armReg n) 0 (by omega) (by omega) (aR_lt s) (aR_lt n) (by omega)]
    rfl

end JT
