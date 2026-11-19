/- Nano/V2Self/Proof/ParRunLoop: Layer-2 FUEL-LOOP defs ↔ ParSpec `pDef`'s loop branch (box B).
`arrows_spec`: the state types (`tyAtom`/`stateTy` loop, 61/74) are `pArrows`; the def row grows by `stAdd` per state. -/
import Nano.V2Self.Proof.ParRunHdr
import Nano.V2Self.Proof.ParRunSelf
namespace ParRun
open ParSpec

/-- stateTy (74): one more state parameter of code `w` -/
def stAdd (c : DefR) (w : Sh) : DefR :=
  let n1 := w == .ls && !hasLs (c.params.map some)
  { c with npw := if n1 then c.npw else c.npw + w.width, params := c.params ++ [w], nni := if n1 then c.nni else c.nni + 1 }

theorem pArrows_succ (f : Nat) (ts : List Tok) : pArrows (f + 1) ts = (pTy f ts).bind fun (t, r) =>
    match r with
    | .k 17 :: r1 => (pArrows f r1).map fun (l, r2) => (t :: l, r2)
    | _ => some ([t], r) := by
  rw [pArrows]; rfl

theorem arrows_spec : ∀ n {ks : List Frame} {st fin : St}, StarN n (.tyAtom :: .stateTy :: ks, st) ([], fin) →
    ∃ (ts : List TyR) (res : TyR) (r : List Tok) (n' : Nat), n' < n ∧ r.length < st.toks.length ∧
      (∀ f, 2 * st.toks.length + 3 ≤ f → pArrows f st.toks = some (ts ++ [res], r)) ∧
      (∀ t ∈ ts, trRes t ≠ .nt ∧ (trRes t).nnt = true) ∧ (trRes res).nnt = true ∧ (ts = [] → st.cur.params.length ≠ 1) ∧
      StarN n' (.armsStart :: ks, { st with toks := r, ty := some (trRes res), cur := (ts.map trRes).foldl stAdd st.cur })
        ([], fin) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro ks st fin h
  obtain ⟨t, r, n1, hn1, hlt, hpTy, h1, hnnt⟩ := (ty_sound n).1 h
  match n1, h1 with
  | 0, h1 => exact absurd h1.zero_nil.1 (by simp)
  | m + 1, h1 =>
  obtain ⟨k, st2, hs, h2⟩ := h1.head
  have hfin : ∀ r', (∀ r'', r' ≠ .k 17 :: r'') → st.cur.params.length ≠ 1 →
      StarN m (.armsStart :: ks, st.withTy r' (trRes t)) ([], fin) → r' = r →
      ∃ (ts : List TyR) (res : TyR) (r : List Tok) (n' : Nat), n' < m + 1 + 0 + 1 ∧ r.length < st.toks.length ∧
      (∀ f, 2 * st.toks.length + 3 ≤ f → pArrows f st.toks = some (ts ++ [res], r)) ∧
      (∀ t ∈ ts, trRes t ≠ .nt ∧ (trRes t).nnt = true) ∧ (trRes res).nnt = true ∧ (ts = [] → st.cur.params.length ≠ 1) ∧
      StarN n' (.armsStart :: ks, { st with toks := r, ty := some (trRes res), cur := (ts.map trRes).foldl stAdd st.cur })
        ([], fin) := by
    intro r' hnot hp h2 e; subst e
    refine ⟨[], t, r', m, by omega, hlt, fun f hf => ?_, by simp, hnnt, fun _ => hp, by simpa [St.withTy] using h2⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [pArrows_succ, hpTy g (by omega)]
    simp only [Option.bind_some]
    first | rfl | (split; · rename_i r'' e; exact absurd e (hnot r''); · rfl)
  have hn : n = m + 1 + 0 + 1 ∨ n > m + 1 := by omega
  clear hn
  cases r with
  | nil =>
    simp only [stepF, St.withTy] at hs
    by_cases hp : st.cur.params.length = 1
    · simp [hp] at hs
    · simp only [hp, if_false, Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨ts, res, r2, n', hn', h'⟩ := hfin [] (by simp) hp (by simpa using h2) rfl
      exact ⟨ts, res, r2, n', by omega, h'⟩
  | cons tk r1 =>
    by_cases h17 : tk = .k 17
    · subst h17
      simp only [stepF, St.withTy] at hs
      by_cases hw : trRes t = .nt
      · simp [hw] at hs
      · simp only [hw, if_false, Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨ts, res, r2, n', hn', hlt2, hp2, hts, hres, hnil, h3⟩ := ih m (by omega) h2
        refine ⟨t :: ts, res, r2, n', by omega, by simp at hlt2 hlt ⊢; omega, fun f hf => ?_, ?_, hres, by simp, ?_⟩
        · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
          rw [pArrows_succ, hpTy g (by omega)]
          simp only [Option.bind_some]
          rw [hp2 g (by simp at hlt hf ⊢; omega)]; rfl
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact ⟨hw, hnnt⟩
          · exact hts u hu
        · simpa [stAdd] using h3
    · have hnot : ∀ r', (tk :: r1) ≠ .k 17 :: r' := by intro r' e; cases e; exact h17 rfl
      have hs' : stepF .stateTy (st.withTy (tk :: r1) (trRes t)) =
          if st.cur.params.length = 1 then none else some ([.armsStart], st.withTy (tk :: r1) (trRes t)) := by
        simp only [stepF, St.withTy]
      rw [hs'] at hs
      by_cases hp : st.cur.params.length = 1
      · simp [hp] at hs
      · simp only [hp, if_false, Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨ts, res, r2, n', hn', h'⟩ := hfin _ hnot hp (by simpa using h2) rfl
        exact ⟨ts, res, r2, n', by omega, h'⟩

end ParRun
