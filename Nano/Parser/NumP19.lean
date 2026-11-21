/- Nano/Parser/NumP19: one def's walk (`u48`): the groups buffer is a permutation of `col`'s groups. -/
import Nano.Parser.NumP18
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- what the walk of a body returns -/
def WQ (gs : List NumSpec.G) (sh : Bool) (e : UInt64) (r : MO) : Prop :=
  r.2.2 = 1 → r.2.1 = e ∧ sh = true ∧ ∃ X, X.Perm gs ∧ r.1 = encG X ∧ (encG X).length < 2 ^ 42

theorem u40_walk {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {body : Nd} {rest : Buf} {i : Nat}
    (hx : x.drop i = body.ser ++ rest) (hi : 0 < i) (hnb : NB np body) (hf : body.ser.length + 1 ≤ 2 ^ 24) :
    WQ (NumSpec.col (2 ^ 24) ks ws [] 1 body).1 (NumSpec.col (2 ^ 24) ks ws [] 1 body).2 (u (i + body.ser.length))
      (u40 16777216 x d bnew 0 (u27 bnew 0 0 1 0) 1 (u i) bnew bnew 0 0) := by
  have hQ : QM (WQ (NumSpec.col (2 ^ 24) ks ws [] 1 body).1 (NumSpec.col (2 ^ 24) ks ws [] 1 body).2
      (u (i + body.ser.length))) := fun r h h1 => absurd h1 h
  have e27 : u27 bnew 0 0 1 0 = [0, 1, 0] := by decide
  have hI : MI bnew [] (u27 bnew 0 0 1 0) ([] ++ [(0, u 1, 0)]) bnew bnew [] := by
    rw [e27]
    exact ⟨by simp [encB, bnew], by simp [bnew], by simp, by simp [encT]; rfl, by simp, by simp [bnew], by simp,
      by simp [bnew]⟩
  have hG := (m_all hK (2 ^ 24)).1 body 1 _ [] [] i rest bnew (u27 bnew 0 0 1 0) bnew bnew [] 0 hf hnb (by omega) hQ hx hi hI
    (by
      intro hsh b' t' g' s' hI' hga n
      cases n with
      | zero => exact hQ _ (show u 0 ≠ 1 by decide)
      | succ n =>
        rw [u40_unf, if_pos (keq (show (u ([] : List T3).length == 0) = true from rfl))]
        intro _
        obtain ⟨X, hX, rfl⟩ := hga
        have := hI'.lg
        exact ⟨rfl, hsh, X, hX, by simp [bnew], by simpa [bnew] using this⟩)
  exact hG 16777216

theorem u48_ok {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {body : Nd} {rest : Buf} {i : Nat}
    (hx : x.drop i = body.ser ++ rest) (hi : 0 < i) (hnb : NB np body) (hf : body.ser.length + 1 ≤ 2 ^ 24) (nn : UInt64) :
    (u48 x d (u i) nn).2 = 1 → (u48 x d (u i) nn).1 = u (i + body.ser.length) ∧
      (NumSpec.col (2 ^ 24) ks ws [] 1 body).2 = true ∧
      ∃ X, X.Perm (NumSpec.col (2 ^ 24) ks ws [] 1 body).1 ∧ (encG X).length < 2 ^ 42 ∧ u50 (encG X) nn = 1 := by
  have hW := u40_walk hK hx hi hnb hf
  unfold u48
  generalize u40 16777216 x d bnew 0 (u27 bnew 0 0 1 0) 1 (u i) bnew bnew 0 0 = W at hW ⊢
  obtain ⟨g, e, ok⟩ := W
  iota_only
  by_cases hok : ok = 1
  · subst hok
    obtain ⟨h1, h2, X, hX, h3, h4⟩ := hW rfl
    simp only at h1 h3
    rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))]
    intro h
    exact ⟨h1, h2, X, hX, h4, by rw [← h3]; exact h⟩
  · rw [if_neg (by simpa using hok)]
    intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

end NumP
