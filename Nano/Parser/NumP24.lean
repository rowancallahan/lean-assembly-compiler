/- Nano/Parser/NumP24: the class check `u50` on the groups buffer `encG X` is the spec's class rule on X. -/
import Nano.Parser.NumP23
namespace NumP
open C ParSpec OwnP

theorem u57_01 : ∀ (m : Nat) (b : Buf) (k : UInt64), (u57 m b k).2 = 0 ∨ (u57 m b k).2 = 1
  | 0, _, _ => Or.inl rfl
  | m + 1, b, k => by
    simp only [u57]
    split
    · exact u57_01 m _ k
    · exact Or.inr rfl

theorem u56_01 : ∀ (m : Nat) (f g : Buf) (q k r : UInt64), (u56 m f g q k r).2 = 0 ∨ (u56 m f g q k r).2 = 1
  | 0, _, _, _, _, _ => Or.inl rfl
  | m + 1, f, g, q, k, r => by
    rw [u56]
    by_cases h : r < k
    · rw [if_pos h]; exact Or.inr rfl
    · rw [if_neg h]
      generalize u55 16777216 f g 0 q k = U
      obtain ⟨f1, ok⟩ := U
      iota_only
      by_cases hok : ok = 1
      · subst hok; rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))]; exact u56_01 m _ g q _ r
      · rw [if_neg (by simpa using hok)]; exact Or.inl rfl

theorem and01 {a b : UInt64} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (h : (a &&& b) = 1) : a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all <;> exact absurd h (by decide)

theorem and01' {a b : UInt64} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : (a &&& b) = 0 ∨ (a &&& b) = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem u50_ok {X : List NumSpec.G} {N : Nat} (hl : (encG X).length < 2 ^ 62) (hX : ∀ G ∈ X, G.d < 3 ∧ ∀ v ∈ G.vs, v < 2 ^ 64)
    (hN : N < 2 ^ 64) : u50 (encG X) (u N) = 1 →
      X.all (gspec (NumSpec.marked 1 X (N + 1) []) (NumSpec.marked 2 X (N + 1) [])) = true := by
  unfold u50
  by_cases hn : u N < 16777215
  rotate_left
  · rw [if_neg hn]; intro h; exact absurd h (by decide)
  rw [if_pos hn]
  have hN' : N < 16777215 := by rw [show (16777215 : UInt64) = u 16777215 from rfl, ult hN (by omega)] at hn; exact hn
  by_cases h51 : u51 16777216 (encG X) 0 (u N) = 1
  rotate_left
  · rw [if_neg (by simpa using h51)]; intro h; exact absurd h (by decide)
  rw [if_pos (by rw [h51]; rfl)]
  have hs := u51_ok (u N) hl 16777216 [] X (by simp) h51
  have hX' : ∀ G ∈ X, G.d < 3 ∧ ∀ v ∈ G.vs, v < N := by
    intro G hG
    refine ⟨(hX G hG).1, fun v hv => ?_⟩
    have := hs G hG v hv
    rwa [ult ((hX G hG).2 v hv) hN] at this
  have z1ok := u57_ok 16777216 bnew N (by omega) (by simp [bnew]) (by simp [bnew])
  have z1b := u57_01 16777216 bnew (u N)
  generalize u57 16777216 bnew (u N) = Z1 at z1ok z1b ⊢
  obtain ⟨z1, k1⟩ := Z1
  iota_only
  simp only at z1ok z1b
  have eN : u N + 1 = u (N + 1) := by rw [u1, uadd]
  rw [eN]
  have fok := u56_ok (X := X) rfl hl 1 (N + 1) (by omega) 16777216 1 z1 (by omega)
  have fb := u56_01 16777216 z1 (encG X) 1 1 (u (N + 1))
  rw [u1e] at fok
  generalize u56 16777216 z1 (encG X) 1 1 (u (N + 1)) = F at fok fb ⊢
  obtain ⟨f, k2⟩ := F
  iota_only
  simp only at fok fb
  have hok := u56_ok (X := X) rfl hl 2 (N + 1) (by omega) 16777216 1 z1 (by omega)
  have hb := u56_01 16777216 z1 (encG X) 2 1 (u (N + 1))
  rw [u1e] at hok
  generalize u56 16777216 z1 (encG X) 2 1 (u (N + 1)) = H at hok hb ⊢
  obtain ⟨h, k4⟩ := H
  iota_only
  simp only at hok hb
  by_cases hk : (k1 &&& k2 &&& k1 &&& k4) = 1
  rotate_left
  · rw [if_neg (by simpa using hk)]; intro h; exact absurd h (by decide)
  rw [if_pos (by rw [hk]; rfl)]
  obtain ⟨hk123, hk4⟩ := and01 (and01' (and01' z1b fb) z1b) hb hk
  obtain ⟨hk12, -⟩ := and01 (and01' z1b fb) z1b hk123
  obtain ⟨hk1, hk2⟩ := and01 z1b fb hk12
  subst hk1 hk2 hk4
  have ef := fok rfl; have eh := hok rfl
  have ez1 := z1ok rfl
  subst ez1
  rw [show N + 1 + 1 - 1 = N + 1 by omega] at ef eh
  have hif : INV 1 X N (0 + (N + 1)) f := by
    rw [ef]; exact rndsN_ok 1 (by omega) X N (by omega) hX' (N + 1) 0 _ (by omega) (inv_zero 1 X N)
  have hih : INV 2 X N (0 + (N + 1)) h := by
    rw [eh]; exact rndsN_ok 2 (by omega) X N (by omega) hX' (N + 1) 0 _ (by omega) (inv_zero 2 X N)
  rw [Nat.zero_add] at hif hih
  intro h58
  have := u58_ok f h hl 16777216 [] X (by simp) h58
  simp only [List.all_eq_true]
  intro G hG
  rw [← gok_spec (by omega) hif hih (hX' G hG)]
  exact this G hG

end NumP
