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

/-- what follows the last binder of an arm -/
def armK : Bool → List Frame
  | true => [.expr 0 1, .mkLoop, .defEnd]
  | false => [.expr 0 0, .zeroDone]

/-- the binding armBind (76) makes for parameter `b` -/
def armBd (st : St) (b : Nat) (x : List Nat) (w : Sh) : Bd :=
  ⟨x, st.sslot, some w, w == .ls && !(hasLs ((st.cur.params.take b).map some))⟩

theorem armBind_inv {stp : Bool} {b : Nat} {st : St} {k : List Frame} {st' : St} (h : stepF (.armBind stp b) st = some (k, st')) :
    ∃ w x t r, st.cur.params[b]? = some w ∧ st.toks = .id x :: t :: r ∧ findB st.binds x = none ∧
      ((b + 1 < st.cur.params.length ∧ t = .k 15 ∧ k = [.armBind stp (b + 1)]) ∨
       (¬ b + 1 < st.cur.params.length ∧ t = .k 19 ∧ k = armK stp)) ∧
      st' = { st with toks := r, binds := st.binds ++ [armBd st b x w],
                      sslot := if (armBd st b x w).inp then st.sslot else st.sslot + w.width } := by
  simp only [stepF] at h
  split at h
  · rename_i w x t r hw ht
    split at h
    · cases h
    · rename_i hb
      split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨w, x, t, r, hw, ht, hb, Or.inl ⟨‹_›, ‹_›, rfl⟩, rfl⟩
        · cases h
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨w, x, t, r, hw, ht, hb, Or.inr ⟨‹_›, ‹_›, by simp_all [armK]⟩, rfl⟩
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨w, x, t, r, hw, ht, hb, Or.inr ⟨‹_›, ‹_›, by simp_all [armK]⟩, rfl⟩
        · cases h
  · cases h

theorem n1_iff (Q : List Sh) (c : Nat) (h : c < Q.length) :
    (Q[c] == .ls && !hasLs (((Sh.nt :: Q).take (c + 1)).map some)) = true ↔ FirstLs Q c := by
  have e : hasLs (((Sh.nt :: Q).take (c + 1)).map some) = hasLs ((Q.take c).map some) := by
    simp [hasLs, List.take_succ_cons]
  rw [e]
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true, hasLs_false_iff]
  unfold FirstLs
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [List.getElem?_eq_getElem h, h1], fun j hj => ?_⟩
    have := h2 j (by simp; omega)
    rwa [List.getElem?_take, if_pos hj] at this
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [List.getElem?_eq_getElem h] at h1; simpa using h1, fun j hj => ?_⟩
    simp at hj
    rw [List.getElem?_take, if_pos (by omega)]; exact h2 j (by omega)

theorem mkEnv_cons (start : Nat) (p : Ps) (ps : List Ps) (x : List Nat) (ns : List (List Nat)) :
    mkEnv start (p :: ps) (x :: ns) = (mkEnv (start + p.width) ps ns).map fun e => (x, start, p) :: e := by
  rw [mkEnv]

theorem armPat_bind (x : List Nat) (r : List Tok) :
    armPat 0 (.k 15 :: .id x :: r) = (armPat 0 r).map fun (l, r') => (x :: l, r') := by rw [armPat]

/-- **arm binders** (76): `x₁ , … , x_k =>` bind the parameters `c+1 …` exactly as `armPat` + `mkEnv` -/
theorem armBind_spec (ps : List Ps) (hfuel : ∀ p ∈ ps, p ≠ .fuel)
    (hinp : ∀ (i : Nat) (h : i < ps.length), (ps[i] = .inp ↔ FirstLs (ps.map psCode) i)) :
    ∀ n {stp : Bool} {c : Nat} {ks : List Frame} {st fin : St}, st.cur.params = .nt :: ps.map psCode → c < ps.length →
      StarN n (.armBind stp (c + 1) :: ks, st) ([], fin) →
      ∃ names env r n' sl, n' < n ∧ armPat 0 (.k 15 :: st.toks) = some (names, r) ∧
        mkEnv st.sslot (ps.drop c) names = some env ∧ (∀ x ∈ names, findB st.binds x = none) ∧ names.Nodup ∧
        r.length < st.toks.length ∧
        StarN n' (armK stp ++ ks, { st with toks := r, binds := st.binds ++ env.map toBd, sslot := sl }) ([], fin) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro stp c ks st fin hP hc h
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | m + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  obtain ⟨w, x, t, r, hw, ht, hb, hk, rfl⟩ := armBind_inv hs
  have hwc : w = psCode ps[c] := by rw [hP] at hw; simp [hc] at hw; exact hw.symm
  have hbd : armBd st (c + 1) x w = toBd (x, st.sslot, ps[c]) := by
    simp only [armBd, toBd, hwc]
    congr 1
    rw [hP]
    have := n1_iff (ps.map psCode) c (by simpa using hc)
    simp only [List.getElem_map] at this
    rw [Bool.eq_iff_iff, this, ← hinp c hc]; simp
  have hsl : (if (armBd st (c + 1) x w).inp then st.sslot else st.sslot + w.width) = st.sslot + ps[c].width := by
    rw [hbd]; simp only [toBd, hwc]
    have := Ps.width_code (hfuel _ (List.getElem_mem hc))
    split <;> simp_all
  rcases hk with ⟨hlt, rfl, rfl⟩ | ⟨hlt, rfl, rfl⟩
  · -- more binders
    have hc1 : c + 1 < ps.length := by rw [hP] at hlt; simpa using hlt
    obtain ⟨names, env, r', n', sl, hn', hpat, henv, hfr, hnd, hlt', h2⟩ :=
      ih m (by omega) (by exact hP) hc1 h1
    simp only at hpat henv hfr hlt' h2
    rw [hsl] at henv
    refine ⟨x :: names, (x, st.sslot, ps[c]) :: env, r', n', sl, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht, armPat_bind, hpat]; rfl
    · rw [List.drop_eq_getElem_cons hc, mkEnv_cons, henv]; rfl
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hb
      · have := hfr y hy
        rw [findB_push] at this
        split at this
        · cases this
        · exact this
    · refine List.nodup_cons.mpr ⟨fun hx => ?_, hnd⟩
      have := hfr x hx
      rw [findB_push] at this
      simp [armBd] at this
    · rw [ht]; simp; omega
    · rw [hbd] at h2; simpa using h2
  · -- the last binder
    have hc1 : c + 1 = ps.length := by rw [hP] at hlt; simp at hlt; omega
    have hdrop : ps.drop c = [ps[c]] := by
      rw [List.drop_eq_getElem_cons hc, List.drop_eq_nil_of_le (by omega)]
    refine ⟨[x], [(x, st.sslot, ps[c])], r, m, st.sslot + ps[c].width, by omega, ?_, ?_, ?_, by simp, ?_, ?_⟩
    · rw [ht, armPat_bind, armPat]; rfl
    · rw [hdrop, mkEnv_cons, mkEnv]; rfl
    · intro y hy; simp at hy; subst hy; exact hb
    · rw [ht]; simp; omega
    · rw [hsl, hbd] at h1; simpa using h1

end ParRun
