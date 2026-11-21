/- E4, layer L3 (FABLE-M4): on Gen's words `c = Cj.map encG` (`JOK` instructions), the nano translator's accessor layer
is the spec's view (`acc20` … `acc24`), hence its atom selection `e35` is the spec's `candC` (`e35_eq`), from the
bit-level facts `JArmBits` (JArmView.lean). -/
import Nano.Run.JArmView
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

theorem e60_eq (a b : UInt64) : e60 a b = eqb a b := rfl
theorem e61_eq (a b : UInt64) : e61 a b = neb a b := rfl

theorem tU_lt {p m : Nat} (hp : p < 2 ^ 64) (hm : m < 2 ^ 64) : (p.toUInt64 < m.toUInt64) ↔ p < m := by
  rw [UInt64.lt_iff_toNat_lt, ArmRA.toU_toNat hp, ArmRA.toU_toNat hm]

theorem tU_succ {q : Nat} (hq : q + 1 < 2 ^ 64) : q.toUInt64 + 1 = (q + 1).toUInt64 := by
  apply ArmRA.u64
  rw [UInt64.toNat_add, ArmRA.toU_toNat (by omega), ArmRA.toU_toNat hq]
  show (q + 1) % 2 ^ 64 = q + 1
  omega

theorem kd_drop (l : List J) (q m : Nat) : kd (l.drop q) m = kd l (q + m) := by
  unfold kd; rw [List.getElem?_drop]
theorem fA_drop (l : List J) (q m : Nat) : fA (l.drop q) m = fA l (q + m) := by
  unfold fA; rw [List.getElem?_drop]
theorem fB_drop (l : List J) (q m : Nat) : fB (l.drop q) m = fB l (q + m) := by
  unfold fB; rw [List.getElem?_drop]
theorem fC_drop (l : List J) (q m : Nat) : fC (l.drop q) m = fC l (q + m) := by
  unfold fC; rw [List.getElem?_drop]
theorem fO_drop (l : List J) (q m : Nat) : fO (l.drop q) m = fO l (q + m) := by
  unfold fO; rw [List.getElem?_drop]

section
variable (B : JArmBits) {Cj : List J} (hJ : ∀ j ∈ Cj, JOK j) (hl : Cj.length < 2 ^ 18)
include B hJ hl

/-- the word at index `p` of Gen's buffer -/
theorem bget_c (p : Nat) (hp : p < 2 ^ 64) :
    bget (Cj.map encG) p.toUInt64 = ((Cj[p]?).map encG).getD 0 := by
  unfold bget
  rw [ArmRA.toU_toNat hp, List.getD_eq_getElem?_getD, List.getElem?_map]

/-- the kind accessor -/
theorem acc20 (p : Nat) (hp : p < 2 ^ 63) :
    e20 (Cj.map encG) (bsize (Cj.map encG)) p.toUInt64 = kd Cj p := by
  have hb : bsize (Cj.map encG) = Cj.length.toUInt64 := by simp [bsize]
  unfold e20 e0 kd
  rw [hb]
  by_cases h : p < Cj.length
  · rw [if_pos ((tU_lt (by omega) (by omega)).2 h), bget_c B hJ hl p (by omega), List.getElem?_eq_getElem h]
    exact B.l2_kind _ (hJ _ (List.getElem_mem h))
  · rw [if_neg (fun h' => h ((tU_lt (by omega) (by omega)).1 h')), List.getElem?_eq_none (by omega)]
    rfl

theorem acc21 (p : Nat) (hp : p < 2 ^ 63) : e21 (Cj.map encG) p.toUInt64 = fA Cj p := by
  have hg := bget_c B hJ hl p (by omega)
  unfold fA
  by_cases h : p < Cj.length
  · rw [List.getElem?_eq_getElem h] at hg ⊢
    exact B.l2_A _ _ _ hg (hJ _ (List.getElem_mem h))
  · rw [List.getElem?_eq_none (by omega)] at hg ⊢
    exact (B.l2_zero _ _ hg).1

theorem acc22 (p : Nat) (hp : p < 2 ^ 63) : e22 (Cj.map encG) p.toUInt64 = fB Cj p := by
  have hg := bget_c B hJ hl p (by omega)
  unfold fB
  by_cases h : p < Cj.length
  · rw [List.getElem?_eq_getElem h] at hg ⊢
    exact B.l2_B _ _ _ hg (hJ _ (List.getElem_mem h))
  · rw [List.getElem?_eq_none (by omega)] at hg ⊢
    exact (B.l2_zero _ _ hg).2.1

theorem acc23 (p : Nat) (hp : p < 2 ^ 63) : e23 (Cj.map encG) p.toUInt64 = fC Cj p := by
  have hg := bget_c B hJ hl p (by omega)
  unfold fC
  by_cases h : p < Cj.length
  · rw [List.getElem?_eq_getElem h] at hg ⊢
    exact B.l2_C _ _ _ hg (hJ _ (List.getElem_mem h))
  · rw [List.getElem?_eq_none (by omega)] at hg ⊢
    exact (B.l2_zero _ _ hg).2.2.1

theorem acc24 (p : Nat) (hp : p < 2 ^ 63) : e24 (Cj.map encG) p.toUInt64 = fO Cj p := by
  have hg := bget_c B hJ hl p (by omega)
  unfold fO
  by_cases h : p < Cj.length
  · rw [List.getElem?_eq_getElem h] at hg ⊢
    exact B.l2_op _ _ _ hg (hJ _ (List.getElem_mem h))
  · rw [List.getElem?_eq_none (by omega)] at hg ⊢
    exact (B.l2_zero _ _ hg).2.2.2

/-- **the translator's atom selection is the spec's**: `e35` at J pc `q` = `candC` of the rest of the program -/
theorem e35_eq (q : Nat) (hq : q < 2 ^ 62) :
    e35 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 = candC (Cj.drop q) := by
  have s1 := tU_succ (q := q) (by omega)
  have k0 := acc20 B hJ hl q (by omega)
  have k1 := acc20 B hJ hl (q + 1) (by omega)
  have a0 := acc21 B hJ hl q (by omega)
  have a1 := acc21 B hJ hl (q + 1) (by omega)
  have b0 := acc22 B hJ hl q (by omega)
  have b1 := acc22 B hJ hl (q + 1) (by omega)
  have c0 := acc23 B hJ hl q (by omega)
  have c1 := acc23 B hJ hl (q + 1) (by omega)
  have o0 := acc24 B hJ hl q (by omega)
  have o1 := acc24 B hJ hl (q + 1) (by omega)
  simp only [e35, candC, e26, e28, e29, m26, m28, m29, e60_eq, e61_eq, s1, k0, k1, a0, a1, b0, b1, c0, c1, o0, o1,
    kd_drop, fA_drop, fB_drop, fC_drop, fO_drop, Nat.add_zero]

end

end JT
