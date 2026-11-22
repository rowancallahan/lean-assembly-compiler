/- Nano/Parser/NumP9: COLSEQ over a list of nodes (pair, prim, call arguments). -/
import Nano.Parser.NumP8
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- `col 1` over a list, joined -/
def colL (f : Nat) (ks ws : List Nat) (env : List Bool) (cs : List Nd) : NumSpec.R :=
  cs.foldr (fun c r => (NumSpec.col f ks ws env 1 c).app r) NumSpec.R.ok

theorem colL_attach (f : Nat) (ks ws : List Nat) (env : List Bool) (cs : List Nd) :
    cs.attach.foldr (fun ⟨c, _⟩ r => (NumSpec.col f ks ws env 1 c).app r) NumSpec.R.ok = colL f ks ws env cs := by
  unfold colL
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.attach_cons, List.foldr_cons, List.foldr_map]; rw [← ih]

theorem MCp.app {x d Q bs ts g S gb c'} {A B : NumSpec.R} {g1 : Buf} (h : MCp x d Q bs ts g S gb c' (A.app B))
    (hA : A.2 = true) (hg : GA g g1 A.1) : MCp x d Q bs ts g1 S gb c' B := by
  intro hB b' t' g' s' hI hga
  exact h (by simp [NumSpec.R.app, hA, hB]) b' t' g' s' hI (hg.trans hga)

/-- COLSEQ over the nodes cs at the cursor -/
theorem m_colseq {x d : Buf} {np : Nat} {ks ws : List Nat} {f : Nat} (hCOL : MCOL x d np ks ws f) {Q : MO → Prop}
    (hQ : QM Q) : ∀ (cs : List Nd) (bs : List (Nat × List Bool)) (ts : List T3) (c : Nat) (rest b t g s : Buf)
    (S : List UInt64) (gb a2 : UInt64),
    (∀ e ∈ cs, e.ser.length + 1 ≤ f) → (∀ e ∈ cs, NB np e) → x.drop c = serL cs ++ rest → 0 < c → cs.length < 2 ^ 32 →
    MI b bs t (ts ++ [(7, u cs.length, a2)]) g s S →
    MCp x d Q bs ts g S gb (c + (serL cs).length) (colL f ks ws (envOf bs) cs) →
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb
  | [], bs, ts, c, rest, b, t, g, s, S, gb, a2, _, _, _, _, _, hI, hP => by
    apply m_colseq0 hQ hI
    intro hI'
    exact hP rfl b t g s hI' (GA.nil g) |>.cast rfl rfl (by simp [serL]) rfl rfl
  | e :: cs, bs, ts, c, rest, b, t, g, s, S, gb, a2, hf, hnb, hx, hc, hl, hI, hP => by
    simp only [List.length_cons] at hI hl
    apply m_colseq1 hQ (by omega) hI
    intro t' hI'
    have hx' : x.drop c = e.ser ++ (serL cs ++ rest) := by rw [hx]; simp [serL]
    refine (hCOL e 1 Q bs (ts ++ [(7, u cs.length, a2)]) c (serL cs ++ rest) b t' g s S gb (hf e (by simp))
      (hnb e (by simp)) (by omega) hQ hx' hc (by rw [show (u 1 : UInt64) = 1 from rfl]; simpa using hI') ?_).cast rfl (by simp) rfl rfl rfl
    intro hA b1 t1 g1 s1 hI1 hga
    have hx2 := drop_shift hx'
    have := m_colseq hCOL hQ cs bs ts (c + e.ser.length) rest b1 t1 g1 s1 S gb a2 (fun e he => hf e (by simp [he]))
      (fun e he => hnb e (by simp [he])) hx2 (by omega) (by omega) (by simpa using hI1)
      (by
        have h2 := MCp.app (A := NumSpec.col f ks ws (envOf bs) 1 e) (B := colL f ks ws (envOf bs) cs)
          (by simpa [colL] using hP) hA hga
        exact (by simpa [serL, Nat.add_assoc] using h2))
    exact this.cast rfl (by simp) rfl rfl rfl

end NumP
