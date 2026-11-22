/- Nano/Parser/NumP24: the class check `u50` on the groups buffer `encG X` is the spec's class rule on X. -/
import Nano.Parser.NumP23
namespace NumP
open C ParSpec OwnP

theorem u57_01 : ∀ (m : Nat) (b : Buf) (j k : UInt64), (u57 m b j k).2 = 0 ∨ (u57 m b j k).2 = 1
  | 0, _, _, _ => Or.inl rfl
  | m + 1, b, j, k => by
    simp only [u57]
    split
    · exact u57_01 m _ _ k
    · exact Or.inr rfl

theorem u56_01 : ∀ (m : Nat) (f g : Buf) (g0 q k r : UInt64), (u56 m f g g0 q k r).2 = 0 ∨ (u56 m f g g0 q k r).2 = 1
  | 0, _, _, _, _, _, _ => Or.inl rfl
  | m + 1, f, g, g0, q, k, r => by
    rw [u56]
    by_cases h : r < k
    · rw [if_pos h]; exact Or.inr rfl
    · rw [if_neg h]
      generalize u55 16777216 f g g0 q k = U
      obtain ⟨f1, ok⟩ := U
      iota_only
      by_cases hok : ok = 1
      · subst hok; rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))]; exact u56_01 m _ g g0 q _ r
      · rw [if_neg (by simpa using hok)]; exact Or.inl rfl

theorem and01 {a b : UInt64} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (h : (a &&& b) = 1) : a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all <;> exact absurd h (by decide)

theorem and01' {a b : UInt64} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : (a &&& b) = 0 ∨ (a &&& b) = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem u50_ok {A X : List NumSpec.G} {N : Nat} {g : Buf} {g0 : UInt64} (hg : g = encG A ++ encG X)
    (hg0 : g0 = bsize (encG A)) (hl : g.length < 2 ^ 62)
    (hX : ∀ G ∈ X, G.d < 3 ∧ ∀ v ∈ G.vs, v < 2 ^ 64) (hN : N < 2 ^ 64) {f h : Buf} (hf : f.length < 2 ^ 62)
    (hh : h.length < 2 ^ 62) :
    (u50 g g0 (u N) f h).1 = 1 →
      X.all (gspec (NumSpec.marked 1 X (N + 1) []) (NumSpec.marked 2 X (N + 1) [])) = true ∧
      (u50 g g0 (u N) f h).2.1.length < 2 ^ 62 ∧ (u50 g g0 (u N) f h).2.2.length < 2 ^ 62 := by
  have hg' : g = encG (A ++ X) := by rw [hg, encG_app]
  have hg0' : g0 = u (encG A).length := by rw [hg0]; rfl
  subst hg0'
  unfold u50
  by_cases hn : u N < 16777215
  rotate_left
  · rw [if_neg hn]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
  rw [if_pos hn]
  have hN' : N < 16777215 := by rw [show (16777215 : UInt64) = u 16777215 from rfl, ult hN (by omega)] at hn; exact hn
  by_cases h51 : u51 16777216 g (u (encG A).length) (u N) = 1
  rotate_left
  · rw [if_neg (by simpa using h51)]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
  rw [if_pos (by rw [h51]; rfl)]
  have hs := u51_ok (u N) hl 16777216 A X hg' h51
  have hX' : ∀ G ∈ X, G.d < 3 ∧ ∀ v ∈ G.vs, v < N := by
    intro G hG
    refine ⟨(hX G hG).1, fun v hv => ?_⟩
    have := hs G hG v hv
    rwa [ult ((hX G hG).2 v hv) hN] at this
  have z1ok := u57_ok 16777216 f 0 N (by omega) (by omega) hf (by omega) (by intro i hi; omega)
  have z1b := u57_01 16777216 f (u 0) (u N)
  rw [show u 0 = (0 : UInt64) from rfl] at z1ok z1b
  generalize u57 16777216 f 0 (u N) = Z1 at z1ok z1b ⊢
  obtain ⟨z1, k1⟩ := Z1
  iota_only
  simp only at z1ok z1b
  have eN : u N + 1 = u (N + 1) := by rw [u1, uadd]
  rw [eN]
  have fok := u56_ok (A := A) (X := X) hg' hl 1 (N + 1) (by omega) 16777216 1 z1 (by omega)
  have fb := u56_01 16777216 z1 g (u (encG A).length) 1 1 (u (N + 1))
  rw [u1e] at fok
  generalize u56 16777216 z1 g (u (encG A).length) 1 1 (u (N + 1)) = F at fok fb ⊢
  obtain ⟨f1, k2⟩ := F
  iota_only
  simp only at fok fb
  have z2ok := u57_ok 16777216 h 0 N (by omega) (by omega) hh (by omega) (by intro i hi; omega)
  have z2b := u57_01 16777216 h (u 0) (u N)
  rw [show u 0 = (0 : UInt64) from rfl] at z2ok z2b
  generalize u57 16777216 h 0 (u N) = Z2 at z2ok z2b ⊢
  obtain ⟨z2, k3⟩ := Z2
  iota_only
  simp only at z2ok z2b
  have hok := u56_ok (A := A) (X := X) hg' hl 2 (N + 1) (by omega) 16777216 1 z2 (by omega)
  have hb := u56_01 16777216 z2 g (u (encG A).length) 2 1 (u (N + 1))
  rw [u1e] at hok
  generalize u56 16777216 z2 g (u (encG A).length) 2 1 (u (N + 1)) = H at hok hb ⊢
  obtain ⟨h1, k4⟩ := H
  iota_only
  simp only at hok hb
  by_cases hk : (k1 &&& k2 &&& k3 &&& k4) = 1
  rotate_left
  · rw [if_neg (by simpa using hk)]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
  rw [if_pos (by rw [hk]; rfl)]
  obtain ⟨hk123, hk4⟩ := and01 (and01' (and01' z1b fb) z2b) hb hk
  obtain ⟨hk12, hk3⟩ := and01 (and01' z1b fb) z2b hk123
  obtain ⟨hk1, hk2⟩ := and01 z1b fb hk12
  subst hk1 hk2 hk3 hk4
  have ef := fok rfl; have eh := hok rfl
  obtain ⟨a1, a2, a3⟩ := z1ok rfl
  obtain ⟨c1, c2, c3⟩ := z2ok rfl
  rw [show N + 1 + 1 - 1 = N + 1 by omega] at ef eh
  have hif : INV 1 X N (0 + (N + 1)) f1 := by
    rw [ef]; exact rndsN_ok 1 (by omega) X N (by omega) hX' (N + 1) 0 _ (by omega)
      (inv_zero 1 X N a1 (by have := a2; omega) a3)
  have hih : INV 2 X N (0 + (N + 1)) h1 := by
    rw [eh]; exact rndsN_ok 2 (by omega) X N (by omega) hX' (N + 1) 0 _ (by omega)
      (inv_zero 2 X N c1 (by have := c2; omega) c3)
  rw [Nat.zero_add] at hif hih
  intro h58
  refine ⟨?_, hif.1.2, hih.1.2⟩
  have := u58_ok f1 h1 hl 16777216 A X hg' h58
  simp only [List.all_eq_true]
  intro G hG
  rw [← gok_spec (by omega) hif hih (hX' G hG)]
  exact this G hG

end NumP
