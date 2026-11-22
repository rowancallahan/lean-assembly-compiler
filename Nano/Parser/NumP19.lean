/- Nano/Parser/NumP19: one def's walk (`u48`): the groups buffer is a permutation of `col`'s groups. -/
import Nano.Parser.NumP18
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- the buffers between defs: sizes -/
structure BI (b t g s y y1 y2 : Buf) : Prop where
  lb : b.length < 2 ^ 44
  lt : t.length < 2 ^ 42
  lg : g.length < 2 ^ 42
  ls : s.length < 2 ^ 42
  sc : SC y y1 y2

/-- what the walk of a body returns (g0: the groups buffer before it) -/
def WQ (g0 : Buf) (gs : List NumSpec.G) (sh : Bool) (e : UInt64) (r : MO) : Prop :=
  r.2.2.1 = 1 → r.2.1 = e ∧ sh = true ∧ ∃ X, X.Perm gs ∧ r.1 = g0 ++ encG X ∧
    BI r.2.2.2.1 r.2.2.2.2.1 r.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2

theorem u40_walk {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {body : Nd} {rest : Buf} {i : Nat}
    (hx : x.drop i = body.ser ++ rest) (hi : 0 < i) (hnb : NB np body) (hf : body.ser.length + 1 ≤ 2 ^ 24)
    {b t g s y y1 y2 : Buf} (hB : BI b t g s y y1 y2) :
    WQ g (NumSpec.col (2 ^ 24) ks ws [] 1 body).1 (NumSpec.col (2 ^ 24) ks ws [] 1 body).2 (u (i + body.ser.length))
      (u40 16777216 x d b 0 (u27 t 0 0 1 0) 1 (u i) g s 0 0 y y1 y2) := by
  have hQ : QM (WQ g (NumSpec.col (2 ^ 24) ks ws [] 1 body).1 (NumSpec.col (2 ^ 24) ks ws [] 1 body).2
      (u (i + body.ser.length))) := fun r h h1 => absurd h1 h
  have hu := u27_ok (ts := []) (t := t) (by simp [encT]) (by have := hB.lt; omega) (by simp) 0 1 0
  have hI : MI b [] (u27 t 0 0 1 0) ([] ++ [(0, u 1, 0)]) g s [] :=
    ⟨by simp [encB], hB.lb, by simp, hu.1, by have h2 : (u27 t 0 0 1 0).length ≤ max t.length 3 := hu.2; have := hB.lt; omega,
      hB.lg, by simp, hB.ls⟩
  have hG := (m_all hK (2 ^ 24)).1 body 1 _ [] [] i rest b (u27 t 0 0 1 0) g s [] 0 hf hnb (by omega) hQ hx hi hI
    (by
      intro hsh b' t' g' s' hI' hga y' y1' y2' hsc n
      cases n with
      | zero => exact hQ _ (show u 0 ≠ 1 by decide)
      | succ n =>
        rw [u40_unf, if_pos (keq (show (u ([] : List T3).length == 0) = true from rfl))]
        intro _
        obtain ⟨X, hX, rfl⟩ := hga
        exact ⟨rfl, hsh, X, hX, rfl, ⟨hI'.lb, by have := hI'.lt; omega, hI'.lg, hI'.ls, hsc⟩⟩)
  exact hG y y1 y2 hB.sc 16777216

theorem u48_ok {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {body : Nd} {rest : Buf} {i : Nat}
    (hx : x.drop i = body.ser ++ rest) (hi : 0 < i) (hnb : NB np body) (hf : body.ser.length + 1 ≤ 2 ^ 24) (nn : UInt64)
    {b t g s y y1 y2 : Buf} (hB : BI b t g s y y1 y2) {A : List NumSpec.G} (hgA : g = encG A) :
    (u48 x d (u i) nn b t g s y y1 y2).2.2.2.2.2.2.1 = 1 → (u48 x d (u i) nn b t g s y y1 y2).1 = u (i + body.ser.length) ∧
      (NumSpec.col (2 ^ 24) ks ws [] 1 body).2 = true ∧
      ∃ X f h, X.Perm (NumSpec.col (2 ^ 24) ks ws [] 1 body).1 ∧ (encG A ++ encG X).length < 2 ^ 42 ∧
        f.length < 2 ^ 62 ∧ h.length < 2 ^ 62 ∧
        (u48 x d (u i) nn b t g s y y1 y2).2.2.2.2.2.2 = u50 (encG A ++ encG X) (bsize (encG A)) nn f h ∧
        (u48 x d (u i) nn b t g s y y1 y2).2.1 = encG A ++ encG X ∧
        (u48 x d (u i) nn b t g s y y1 y2).2.2.1.length < 2 ^ 44 ∧
        (u48 x d (u i) nn b t g s y y1 y2).2.2.2.1.length < 2 ^ 42 ∧
        (u48 x d (u i) nn b t g s y y1 y2).2.2.2.2.1.length < 2 ^ 42 ∧
        (u48 x d (u i) nn b t g s y y1 y2).2.2.2.2.2.1.length < 2 ^ 62 := by
  have hW := u40_walk hK hx hi hnb hf hB
  unfold u48
  zeta_only
  subst hgA
  generalize u40 16777216 x d b 0 (u27 t 0 0 1 0) 1 (u i) (encG A) s 0 0 y y1 y2 = W at hW ⊢
  obtain ⟨g1, e, ok, b1, t1, s1, y3, y4, y5⟩ := W
  iota_only
  by_cases hok : ok = 1
  · subst hok
    obtain ⟨h1, h2, X, hX, h3, hB1⟩ := hW rfl
    simp only at h1 h3 hB1
    subst h3
    rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))]
    intro _
    exact ⟨h1, h2, X, y3, y4, hX, hB1.lg, hB1.sc.1, hB1.sc.2.1, rfl, rfl, hB1.lb, hB1.lt, hB1.ls, hB1.sc.2.2⟩
  · rw [if_neg (by simpa using hok)]
    intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

end NumP
