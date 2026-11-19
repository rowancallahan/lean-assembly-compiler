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

theorem hasLs_snoc (ps : List Sh) (w : Sh) : hasLs ((ps ++ [w]).map some) = (hasLs (ps.map some) || w == .ls) := by
  simp only [hasLs, List.map_append, List.any_append, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false]
  cases w <;> simp

/-- the row after the state types: parameters / width are `stateKinds`' -/
theorem fold_stAdd : ∀ (ts : List TyR), (∀ t ∈ ts, t ≠ .sh .ls) → ∀ c : DefR,
    ((ts.map trRes).foldl stAdd c).params = c.params ++ (stateKinds (hasLs (c.params.map some)) ts).map psCode ∧
    ((ts.map trRes).foldl stAdd c).npw = c.npw + ((stateKinds (hasLs (c.params.map some)) ts).map Ps.width).sum ∧
    ((ts.map trRes).foldl stAdd c).name = c.name ∧ ((ts.map trRes).foldl stAdd c).res = c.res ∧
    ((ts.map trRes).foldl stAdd c).loop = c.loop
  | [], _, c => by simp [stateKinds]
  | t :: ts, hl, c => by
    have ht : t ≠ .sh .ls := hl t (by simp)
    obtain ⟨h1, h2, h3, h4, h5⟩ := fold_stAdd ts (fun u hu => hl u (by simp [hu])) (stAdd c (trRes t))
    simp only [List.map_cons, List.foldl_cons]
    have hu : hasLs ((stAdd c (trRes t)).params.map some) = (pickPs (hasLs (c.params.map some)) true t).2 := by
      simp only [stAdd, hasLs_snoc]
      cases t with
      | sh s => cases s <;> simp_all [pickPs, trRes]
      | lst => cases hh : hasLs (c.params.map some) <;> simp [pickPs, trRes]
    rw [hu] at h1 h2
    refine ⟨?_, ?_, by rw [h3]; rfl, by rw [h4]; rfl, by rw [h5]; rfl⟩
    · rw [h1]; simp only [stAdd, stateKinds, List.map_cons, List.append_assoc, List.singleton_append]
      congr 2
      cases t with
      | sh s => rfl
      | lst => cases hasLs (c.params.map some) <;> rfl
    · rw [h2]; simp only [stAdd, stateKinds, List.map_cons, List.sum_cons]
      cases t with
      | sh s =>
        have : s ≠ .ls := fun e => ht (by rw [e])
        simp [pickPs, trRes, this, Ps.width]; omega
      | lst => cases hh : hasLs (c.params.map some) <;> simp [pickPs, trRes, hh, Ps.width, Sh.width] <;> omega

theorem stateKinds_length : ∀ (u : Bool) (ts : List TyR), (stateKinds u ts).length = ts.length
  | _, [] => rfl
  | u, t :: ts => by simp [stateKinds, stateKinds_length _ ts]

theorem firstLs_cons_zero (w : Sh) (ws : List Sh) : FirstLs (w :: ws) 0 ↔ w = .ls := by
  simp [FirstLs]

theorem firstLs_cons_succ (w : Sh) (ws : List Sh) (i : Nat) : FirstLs (w :: ws) (i + 1) ↔ w ≠ .ls ∧ FirstLs ws i := by
  unfold FirstLs
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun e => h2 0 (by omega) (by simp [e]), by simpa using h1, fun j hj => ?_⟩
    have := h2 (j + 1) (by omega); simpa using this
  · rintro ⟨hw, h1, h2⟩
    refine ⟨by simpa using h1, fun j hj => ?_⟩
    cases j with
    | zero => simp [hw]
    | succ j => simpa using h2 j (by omega)

/-- the input state is the first List state (and none if a List came before) -/
theorem stateKinds_inp : ∀ (ts : List TyR), (∀ t ∈ ts, t ≠ .sh .ls) → ∀ (u : Bool) (i : Nat) (h : i < (stateKinds u ts).length),
    ((stateKinds u ts)[i] = .inp ↔ (u = false ∧ FirstLs (ts.map trRes) i))
  | [], _, _, i, h => by simp [stateKinds] at h
  | t :: ts, hl, u, i, h => by
    have ht : t ≠ .sh .ls := hl t (by simp)
    cases i with
    | zero =>
      simp only [stateKinds, List.getElem_cons_zero, List.map_cons, firstLs_cons_zero]
      cases t with
      | sh s =>
        have : s ≠ .ls := fun e => ht (by rw [e])
        simp [pickPs, trRes, this]
      | lst => cases u <;> simp [pickPs, trRes]
    | succ i =>
      simp only [stateKinds, List.getElem_cons_succ, List.map_cons, firstLs_cons_succ]
      rw [stateKinds_inp ts (fun v hv => hl v (by simp [hv])) _ i (by simpa [stateKinds] using h)]
      cases t with
      | sh s =>
        have : s ≠ .ls := fun e => ht (by rw [e])
        simp [pickPs, trRes, this]
      | lst => cases u <;> simp [pickPs, trRes]

end ParRun
