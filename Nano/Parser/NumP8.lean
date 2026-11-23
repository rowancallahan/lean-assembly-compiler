/- Nano/Parser/NumP8: COL at a literal-only node. -/
import Nano.Parser.NumP7
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- COL at a literal-only node: open a group, LIT, CLOSE -/
theorem m_col_lit {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hLIT : MLIT x d np ks ws f)
    {e : Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S : List UInt64} {gb : UInt64}
    (hf : e.ser.length ≤ f) (hnb : NB np e) (hdd : dd < 3) (hQ : QM Q) (hx : x.drop c = e.ser ++ rest) (hc : 0 < c)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) e = true)
    (hP : MCp x d Q bs ts g S gb (c + e.ser.length) (NumSpec.col (f + 1) ks ws (envOf bs) dd e)) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_read hQ (Or.inl rfl) hI
  intro hsz y y1 y2 hsc R hR
  subst hR
  have hU := u32_ok hK.lc hf hnb hx hc hI.pb (by have := hsz.1; omega) hI.sb hsc.1 hsc.2.1
  generalize hUe : u32 x d b (u (encB bs).length) y y1 (u c) = U at hU
  obtain ⟨b1, r, y3, y4⟩ := U
  rw [u49_0, u41_eq hUe]
  by_cases hr2 : r = 2
  · subst hr2; rw [if_pos (keq rfl)]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
  obtain ⟨hr, hb1, hbl1, hy3, hy4⟩ := hU hr2
  simp only at hr hb1 hbl1 hy3 hy4
  rw [hl] at hr; subst hr
  rw [if_neg (kne (show (w2 true == 2) = false from rfl)), if_pos (keq (show (w2 true == 1) = true from rfl))]
  intro _
  refine ⟨⟨by dsimp only; omega, by dsimp only; omega, hsc.2.2⟩, ?_⟩
  dsimp only
  have hts := hI.lts; simp at hts
  obtain ⟨h1, l1⟩ := hI.pop.pushw rfl (by have := hsz.2.1; omega) 4 (u dd) gb
  generalize ht1 : u27 t (u ts.length) 4 (u dd) gb = t1 at h1 l1
  obtain ⟨h2, l2⟩ := h1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 1 0 0
  generalize ht2 : u27 t1 (u ts.length + 1) 1 0 0 = t2 at h2 l2
  obtain ⟨h3, -⟩ := h2.spush (by have := hsz.2.2.2; omega) (w2 false)
  generalize hs1 : u20 s (u S.length) (w2 false) = s1 at h3
  have hI' : MI b1 bs t2 ((ts ++ [(4, u dd, gb)]) ++ [(1, 0, 0)]) g s1 (S ++ w2 false :: []) :=
    ⟨hb1, by omega, h3.sb, h3.pt, h3.lt, h3.lg, h3.ps, h3.ls⟩
  have e1 : u ts.length + 2 = u ((ts ++ [(4, u dd, gb)]).length + 1) := by simp [u2, uadd]
  have e2 : u S.length + 1 = u (S ++ w2 false :: []).length := by simp [u1, uadd]
  have e3 : u20 s (u S.length) 0 = s1 := hs1
  rw [e1, e2, e3]
  refine hLIT e Q bs (ts ++ [(4, u dd, gb)]) c rest b1 t2 g s1 S false [] hf hnb hQ hx hc hI' ?_
  intro hr2 b' t' g' s' hI2 hga
  generalize hL : NumSpec.litG f ks ws (envOf bs) e = L at hr2 hI2 hga ⊢
  rw [Bool.false_or, List.nil_append] at hI2 ⊢
  rw [List.length_append, List.length_singleton]
  refine m_close hQ (by omega) (S0 := S) (SL := L.1.1) hI2 ?_
  intro hI3
  rw [col_succ, if_pos hl, hL] at hP
  refine hP hr2 _ _ _ _ hI3 ?_
  obtain ⟨X, hX, rfl⟩ := hga
  refine ⟨X ++ [⟨L.1.1, dd, L.1.2⟩], ?_, by simp [encG]⟩
  exact (List.perm_append_singleton _ _).trans (List.Perm.cons _ hX)

end NumP
