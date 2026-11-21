/- Nano/Parser/NumP4: `u31` / `u32` (lw and isL of a node), `u17` (spineLet), `u16` (leaves), `u33` (shapeOk). -/
import Nano.Parser.NumP3
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- what a run of the lw machine from a node returns -/
def LR (bs : List (Nat × List Bool)) (L : List UInt64) (c' : Nat) (r : LO) : Prop :=
  r.2.2.2.2 = 1 → encB bs <+: r.1 ∧ r.1.length < 2 ^ 42 ∧ L <+: r.2.1 ∧ r.2.1.length < 2 ^ 42 ∧ r.2.2.1 = u L.length ∧
    r.2.2.2.1 = u c'

/-- `u31`: lw of the node at c -/
theorem u31_ok {x d : Buf} {np : Nat} {ws : List Nat} (hC : LC x d ws) {f : Nat} {e : Nd} {rest : Buf} {c : Nat}
    {bs : List (Nat × List Bool)} {b : Buf} (hf : e.ser.length ≤ f) (hnb : NB np e) (hx : x.drop c = e.ser ++ rest)
    (hc : 0 < c) (hb : encB bs <+: b) (hbl : b.length < 2 ^ 42) (hs : ∀ r ∈ bs, r.1 < 2 ^ 32) :
    LR bs ((NumSpec.lw f ws (envOf bs) e).map w2) (c + e.ser.length) (u31 x d b (u (encB bs).length) (u c)) := by
  have hQ : QE (LR bs ((NumSpec.lw f ws (envOf bs) e).map w2) (c + e.ser.length)) := fun r h h1 => absurd h1 h
  have e27 : u27 bnew 0 0 0 0 = [0, 0, 0] := by decide
  have h0 : LI b bs bnew [] (u27 bnew 0 0 0 0) ([] ++ [(0, 0, 0)]) := by
    rw [e27]; exact ⟨hb, hbl, List.nil_prefix, by simp [bnew], by simp [encT], by simp, hs⟩
  have := lw_all hC f e _ bs [] [] c rest b bnew (u27 bnew 0 0 0 0) hf hnb hQ hx hc h0 (by
    intro b1 v1 t1 hI n
    cases n with
    | zero => exact hQ _ (by simp [u28])
    | succ n =>
      simp only [List.nil_append, List.length_nil, show u 0 = 0 from rfl, u28, show ((0 : UInt64) == 0) = true from rfl,
        if_true]
      intro _
      exact ⟨hI.pb, hI.lb, by simpa using hI.pv, hI.lv, by simp, rfl⟩)
  exact this 16777216

/-- `u32`: isL of the node at c (1 / 0; 2 error) -/
theorem u32_ok {x d : Buf} {np : Nat} {ws : List Nat} (hC : LC x d ws) {f : Nat} {e : Nd} {rest : Buf} {c : Nat}
    {bs : List (Nat × List Bool)} {b : Buf} (hf : e.ser.length ≤ f) (hnb : NB np e) (hx : x.drop c = e.ser ++ rest)
    (hc : 0 < c) (hb : encB bs <+: b) (hbl : b.length < 2 ^ 42) (hs : ∀ r ∈ bs, r.1 < 2 ^ 32) :
    (u32 x d b (u (encB bs).length) (u c)).2 ≠ 2 →
      (u32 x d b (u (encB bs).length) (u c)).2 = w2 (NumSpec.isL f ws (envOf bs) e) ∧
      encB bs <+: (u32 x d b (u (encB bs).length) (u c)).1 ∧ (u32 x d b (u (encB bs).length) (u c)).1.length < 2 ^ 42 := by
  have h := u31_ok hC hf hnb hx hc hb hbl hs
  unfold u32
  generalize u31 x d b _ _ = R at h ⊢
  obtain ⟨b1, v, vt, e', ok⟩ := R
  simp only [LR] at h ⊢
  by_cases hok : ok = 1
  · subst hok
    obtain ⟨p1, p2, p3, p3', p4, -⟩ := h rfl
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    intro _
    refine ⟨?_, p1, p2⟩
    subst p4
    unfold NumSpec.isL
    generalize NumSpec.lw f ws (envOf bs) e = L at p3 ⊢
    have hl : L.length < 2 ^ 42 := by have := p3.length_le; simp at this; omega
    rcases L with _ | ⟨a, _ | ⟨a', L⟩⟩
    · simp [show (u 0 == 1) = false from rfl, w2]
    · have : bget v 0 = w2 a := by
        rw [show (0 : UInt64) = u 0 from rfl, bget_pre p3 (by simp) (by omega)]; rfl
      simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, show (u (0 + 1) == 1) = true from rfl, if_true, this]
      cases a <;> rfl
    · have : (u (L.length + 1 + 1) == 1) = false := by rw [u1, ueq (by simp at hl; omega) (by omega)]; simp
      simp only [List.map_cons, List.length_cons, List.length_map, this]
      simp [w2]
  · simp only [show (ok == 1) = false by simpa using hok, Bool.false_eq_true, if_false]
    intro h2; exact absurd rfl h2

end NumP
