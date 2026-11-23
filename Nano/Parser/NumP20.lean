/- Nano/Parser/NumP20: the class check's slot loops (`u52`, `u53`, `u54`, `u59`) and `u57`. -/
import Nano.Parser.NumP19
namespace NumP
open C ParSpec OwnP

theorem u52_ok : ∀ (m : Nat) (L W g : Buf) (n : UInt64), W ++ L <+: g → g.length < 2 ^ 62 →
    u52 m g (u W.length) (u (W.length + L.length)) n = 1 → ∀ w ∈ L, w < n
  | 0, _, _, _, _, _, _, h => by simp [u52] at h
  | m + 1, [], W, g, n, _, _, _ => by simp
  | m + 1, w :: L, W, g, n, hv, hl, h => by
    have hl2 := hv.length_le; simp at hl2
    have c1 : (u W.length < u (W.length + (w :: L).length)) = True := by
      rw [ult (by omega) (by simp; omega)]; simp
    have r1 : bget g (u W.length) = w := by
      rw [bget_pre hv (by simp) (by omega)]; simp [List.getD_eq_getElem?_getD]
    have e2 : u W.length + 1 = u (W ++ [w]).length := by simp [u1, uadd]
    have e3 : u (W.length + (w :: L).length) = u ((W ++ [w]).length + L.length) := by
      simp only [List.length_cons, List.length_append, List.length_nil]; congr 1; omega
    simp only [u52, c1, if_true, r1] at h
    by_cases hw : w < n
    · rw [if_pos hw, e2, e3] at h
      have := u52_ok m L (W ++ [w]) g n (by simpa using hv) hl h
      intro w' hw'; simp at hw'; rcases hw' with rfl | hw'
      · exact hw
      · exact this w' hw'
    · rw [if_neg hw] at h; exact absurd h (by decide)

/-- `u59`: some slot is marked -/
theorem u59_ok (f : Buf) : ∀ (m : Nat) (L W g : Buf), W ++ L <+: g → g.length < 2 ^ 62 →
    u59 m f g (u W.length) (u (W.length + L.length)) = 2 ∨
      u59 m f g (u W.length) (u (W.length + L.length)) = w2 (L.any fun w => bget f w != 0)
  | 0, _, _, _, _, _ => Or.inl rfl
  | m + 1, [], W, g, hv, _ => by
    right
    have := hv.length_le; simp at this
    have : (u W.length < u (W.length + 0)) = False := by rw [ult (by omega) (by omega)]; simp
    simp only [u59, List.length_nil, this, if_false]; rfl
  | m + 1, w :: L, W, g, hv, hl => by
    have hl2 := hv.length_le; simp at hl2
    have c1 : (u W.length < u (W.length + (w :: L).length)) = True := by
      rw [ult (by omega) (by simp; omega)]; simp
    have r1 : bget g (u W.length) = w := by
      rw [bget_pre hv (by simp) (by omega)]; simp [List.getD_eq_getElem?_getD]
    have e2 : u W.length + 1 = u (W ++ [w]).length := by simp [u1, uadd]
    have e3 : u (W.length + (w :: L).length) = u ((W ++ [w]).length + L.length) := by
      simp only [List.length_cons, List.length_append, List.length_nil]; congr 1; omega
    simp only [u59, c1, if_true, r1]
    by_cases hw : bget f w = 0
    · rw [if_pos (by simp [hw]), e2, e3]
      rcases u59_ok f m L (W ++ [w]) g (by simpa using hv) hl with h | h
      · exact Or.inl h
      · right; rw [h]; simp [hw]
    · rw [if_neg (by simpa using hw)]; right; simp [hw, w2]

/-- `u53`: some slot was marked before round k -/
theorem u53_ok (f : Buf) (k : UInt64) : ∀ (m : Nat) (L W g : Buf), W ++ L <+: g → g.length < 2 ^ 62 →
    u53 m f g (u W.length) (u (W.length + L.length)) k = 2 ∨
      u53 m f g (u W.length) (u (W.length + L.length)) k = w2 (L.any fun w => bget f w != 0 && decide (bget f w < k))
  | 0, _, _, _, _, _ => Or.inl rfl
  | m + 1, [], W, g, hv, _ => by
    right
    have := hv.length_le; simp at this
    have : (u W.length < u (W.length + 0)) = False := by rw [ult (by omega) (by omega)]; simp
    simp only [u53, List.length_nil, this, if_false]; rfl
  | m + 1, w :: L, W, g, hv, hl => by
    have hl2 := hv.length_le; simp at hl2
    have c1 : (u W.length < u (W.length + (w :: L).length)) = True := by
      rw [ult (by omega) (by simp; omega)]; simp
    have r1 : bget g (u W.length) = w := by
      rw [bget_pre hv (by simp) (by omega)]; simp [List.getD_eq_getElem?_getD]
    have e2 : u W.length + 1 = u (W ++ [w]).length := by simp [u1, uadd]
    have e3 : u (W.length + (w :: L).length) = u ((W ++ [w]).length + L.length) := by
      simp only [List.length_cons, List.length_append, List.length_nil]; congr 1; omega
    have ih := u53_ok f k m L (W ++ [w]) g (by simpa using hv) hl
    simp only [u53, c1, if_true, r1]
    rw [e2, e3]
    by_cases hw : bget f w = 0
    · rw [if_pos (by simp [hw])]
      rcases ih with h | h
      · exact Or.inl h
      · right; rw [h]; simp [hw]
    · rw [if_neg (by simpa using hw)]
      by_cases hk : bget f w < k
      · rw [if_pos hk]; right; simp [hw, hk, w2]
      · rw [if_neg hk]
        rcases ih with h | h
        · exact Or.inl h
        · right; rw [h]; simp [hw, hk]

/-- `u54`: mark the unmarked slots with k -/
def mk54 (k : UInt64) (f : Buf) (L : List UInt64) : Buf := L.foldl (fun f w => if bget f w == 0 then bset f w k else f) f

theorem u54_ok (k : UInt64) : ∀ (m : Nat) (L W g f : Buf), W ++ L <+: g → g.length < 2 ^ 62 →
    (u54 m f g (u W.length) (u (W.length + L.length)) k).2 = 1 →
      (u54 m f g (u W.length) (u (W.length + L.length)) k).1 = mk54 k f L
  | 0, _, _, _, _, _, _, h => by simp [u54] at h
  | m + 1, [], W, g, f, hv, _, _ => by
    have := hv.length_le; simp at this
    have : (u W.length < u (W.length + 0)) = False := by rw [ult (by omega) (by omega)]; simp
    simp [u54, this, mk54]
  | m + 1, w :: L, W, g, f, hv, hl, h => by
    have hl2 := hv.length_le; simp at hl2
    have c1 : (u W.length < u (W.length + (w :: L).length)) = True := by
      rw [ult (by omega) (by simp; omega)]; simp
    have r1 : bget g (u W.length) = w := by
      rw [bget_pre hv (by simp) (by omega)]; simp [List.getD_eq_getElem?_getD]
    have e2 : u W.length + 1 = u (W ++ [w]).length := by simp [u1, uadd]
    have e3 : u (W.length + (w :: L).length) = u ((W ++ [w]).length + L.length) := by
      simp only [List.length_cons, List.length_append, List.length_nil]; congr 1; omega
    simp only [u54, c1, if_true, r1] at h ⊢
    rw [e2, e3] at h ⊢
    by_cases hw : bget f w = 0
    · rw [if_pos (by simp [hw])] at h ⊢
      rw [u54_ok k m L (W ++ [w]) g _ (by simpa using hv) hl h]
      simp [mk54, hw]
    · rw [if_neg (by simpa using hw)] at h ⊢
      rw [u54_ok k m L (W ++ [w]) g _ (by simpa using hv) hl h]
      simp [mk54, hw]

/-- `u57`: zero words j .. n -/
theorem u57_ok : ∀ (m : Nat) (b : Buf) (j n : Nat), j ≤ n → n < 2 ^ 62 → b.length < 2 ^ 62 → j ≤ b.length →
    (∀ i, i < j → b.getD i 0 = 0) → (u57 m b (u j) (u n)).2 = 1 →
    n ≤ (u57 m b (u j) (u n)).1.length ∧ (u57 m b (u j) (u n)).1.length ≤ max b.length n ∧
      ∀ i, i < n → (u57 m b (u j) (u n)).1.getD i 0 = 0
  | 0, _, _, _, _, _, _, _, _, h => by simp [u57] at h
  | m + 1, b, j, n, hjn, hn, hb, hjb, hz, h => by
    have hc : (u j < u n) = (j < n) := ult (by omega) (by omega)
    simp only [u57, hc] at h ⊢
    by_cases hlt : j < n
    · rw [if_pos hlt] at h ⊢
      have e1 : u j + 1 = u (j + 1) := by rw [u1, uadd]
      have hw : u20 b (u j) 0 = OwnP.wr b j 0 := u20_eq b (by omega) (by omega) 0
      rw [e1, hw] at h ⊢
      have hl := OwnP.wr_length hjb (0 : UInt64)
      have ih := u57_ok m (OwnP.wr b j 0) (j + 1) n (by omega) hn (by omega) (by omega)
        (by intro i hi; rw [OwnP.wr_getD hjb]; split
            · rfl
            · exact hz i (by omega)) h
      exact ⟨ih.1, by have := ih.2.1; omega, ih.2.2⟩
    · rw [if_neg hlt]
      dsimp only
      exact ⟨by omega, by omega, fun i hi => hz i (by omega)⟩

end NumP
