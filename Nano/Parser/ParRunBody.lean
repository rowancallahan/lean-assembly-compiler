/- Nano/Parser/ParRunBody: Layer-2 plain def body (parser lead), pure.  `body_spec`: `plainBody` reads `:=`, records npw / res /
loop in the current row, and B's expression lemma (`expr_specs`) gives the body value and the spec's `pExpr`; the run continues at
`defEnd`. -/
import Nano.Parser.ParRunHdr
import Nano.Parser.ParRunSelf
namespace ParRun
open ParSpec

/-- G's `CxRel` does not look at the current row or the tokens while the arm flag is off -/
theorem CxRel.cur_change {st : St} {cx : Cx} (h : CxRel st cx) (harm : st.arm = false) (c : DefR) (r : List Tok) :
    CxRel { st with cur := c, toks := r } cx := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun e => absurd e (by simp [harm])⟩

/-- the current row after `plainBody` / `afterColon`'s `:=` -/
def bodyRow (st : St) : DefR := { st.cur with npw := st.nx, res := st.ty, loop := false }

/-- **plain body** -/
theorem body_spec {n : Nat} {ks : List Frame} {st fin : St} {cx : Cx} {w : Sh} (h : StarN n (.plainBody :: ks, st) ([], fin))
    (hty : st.ty = some w) (hc : CxRel st cx) (harm : st.arm = false) (hn : CxNN { st with cur := bodyRow st }) :
    ∃ r4 v st' n', n' < n ∧ st.toks = .k 9 :: r4 ∧ w ≠ .nt ∧ Post { st with cur := bodyRow st, toks := r4 } st' st.vals v ∧
      Star (.plainBody :: ks, st) (.defEnd :: ks, st') ∧
      StarN n' (.defEnd :: ks, st') ([], fin) ∧ Star ([.expr 0 0], { st with cur := bodyRow st, toks := r4 }) ([], st') ∧
      ShNN v.sh ∧ Stop 0 st'.toks ∧
      (VT (rows { st with cur := bodyRow st }) v → ∃ ty, TyRel v ty ∧ PT v ∧
        ∀ f, 4 * r4.length + 4 ≤ f → pExpr f cx false r4 st.nx = some (v.toNd, ty, st'.toks, st'.nx)) := by
  match n, h with
  | n + 1, h =>
    obtain ⟨k, st1, h1, h2⟩ := h.head
    have hs0 := Star.one (fs := ks) h1
    have hw : w ≠ .nt := by
      intro e; subst e; simp [stepF, hty] at h1
    obtain ⟨r4, ht⟩ : ∃ r4, st.toks = .k 9 :: r4 := by
      rcases ht : st.toks with _ | ⟨tk, r4⟩
      · simp [stepF, hty, hw, ht] at h1
      · cases tk with
        | k c =>
          by_cases hc9 : c = 9
          · subst hc9; exact ⟨r4, rfl⟩
          · simp [stepF, hty, hw, ht, hc9] at h1
        | num v => simp [stepF, hty, hw, ht] at h1
        | id x => simp [stepF, hty, hw, ht] at h1
    simp [stepF, hty, hw, ht] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simp only [List.cons_append, List.nil_append] at hs0
    have hc' := hc.cur_change harm (bodyRow st) r4
    have hn' : CxNN { st with cur := bodyRow st, toks := r4 } := hn
    obtain ⟨st'', n1, n2, hn12, e1, e2⟩ := StarN.split (k := [.expr 0 0]) (ks := .defEnd :: ks) h2
    obtain ⟨v, st', n', hn', hP, _, h3, hS, hNN, hV⟩ := (expr_specs n1).2.2.2 0 [] _ st'' cx (by decide)
      (by simpa [bodyRow, hty] using e1) (by simpa [bodyRow, hty] using hc') (by simpa [bodyRow, hty] using hn')
    obtain ⟨rfl, he⟩ := StarN.nil_inv h3
    have e3 : st' = st'' := by have := congrArg Prod.snd he; simpa using this.symm
    subst e3
    refine ⟨r4, v, st', n2, by omega, ht, hw, by simpa [bodyRow, hty] using hP,
      hs0.trans (by simpa using Star.append (.defEnd :: ks) e1.toStar), e2, by simpa [bodyRow, hty] using e1.toStar,
      hNN, hS, fun hvt => ?_⟩
    obtain ⟨ty, h4, h5, h6⟩ := hV (by simpa [bodyRow, hty, rows] using hvt)
    exact ⟨ty, h4, h5, fun f hf => by simpa using h6 f (by simpa using hf)⟩

end ParRun
