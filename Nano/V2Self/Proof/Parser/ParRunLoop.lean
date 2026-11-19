/- Nano/V2Self/Proof/Parser/ParRunLoop: Layer-2 FUEL-LOOP defs ↔ ParSpec `pDef`'s loop branch (box B).
`arrows_spec`: the state types (`tyAtom`/`stateTy` loop, 61/74) are `pArrows`; the def row grows by `stAdd` per state. -/
import Nano.V2Self.Proof.Parser.ParRunHdr
import Nano.V2Self.Proof.Parser.ParRunSelf
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

/-- `ExprSpec` plus the run prefix as a `Star` (an expression frame is self-contained) -/
theorem expr_star {n md : Nat} {ks : List Frame} {st fin : St} {cx : Cx} (hmd : md < 2)
    (h : StarN n (.expr 0 md :: ks, st) ([], fin)) (hc : CxRel st cx) (hnn : CxNN st) :
    ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧
      Stop 0 st'.toks ∧ ShNN v.sh ∧
      (VT (rows st) v → ∃ ty, TyRel v ty ∧ PT v ∧
        ∀ f, 4 * st.toks.length + 4 ≤ f → pExpr f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx)) ∧
      Star (.expr 0 md :: ks, st) (ks, st') := by
  obtain ⟨X, n1, n2, hn, e1, e2⟩ := StarN.split (k := [.expr 0 md]) (ks := ks) h
  obtain ⟨v, st', n', hn', hP, hlt, h3, hS, hNN, hV⟩ := (expr_specs n1).2.2.2 md [] _ X cx hmd e1 hc hnn
  obtain ⟨rfl, he⟩ := StarN.nil_inv h3
  have eX : st' = X := by have := congrArg Prod.snd he; simpa using this.symm
  subst eX
  exact ⟨v, st', n2, by omega, hP, hlt, e2, hS, hNN, hV, by simpa using Star.append ks e1.toStar⟩

theorem arrows_spec : ∀ n {ks : List Frame} {st fin : St}, StarN n (.tyAtom :: .stateTy :: ks, st) ([], fin) →
    ∃ (ts : List TyR) (res : TyR) (r : List Tok) (n' : Nat), n' < n ∧ r.length < st.toks.length ∧
      (∀ f, 2 * st.toks.length + 3 ≤ f → pArrows f st.toks = some (ts ++ [res], r)) ∧
      (∀ t ∈ ts, trRes t ≠ .nt ∧ (trRes t).nnt = true) ∧ (trRes res).nnt = true ∧ (ts = [] → st.cur.params.length ≠ 1) ∧
      StarN n' (.armsStart :: ks, { st with toks := r, ty := some (trRes res), cur := (ts.map trRes).foldl stAdd st.cur })
        ([], fin) ∧
      Star (.tyAtom :: .stateTy :: ks, st)
        (.armsStart :: ks, { st with toks := r, ty := some (trRes res), cur := (ts.map trRes).foldl stAdd st.cur }) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro ks st fin h
  obtain ⟨t, r, n1, hn1, hlt, hpTy, hT, h1, hnnt⟩ := ty_star h
  match n1, h1 with
  | 0, h1 => exact absurd h1.zero_nil.1 (by simp)
  | m + 1, h1 =>
  obtain ⟨k, st2, hs, h2⟩ := h1.head
  have hs0 := hs
  have hfin : ∀ r', (∀ r'', r' ≠ .k 17 :: r'') → st.cur.params.length ≠ 1 →
      StarN m (.armsStart :: ks, st.withTy r' (trRes t)) ([], fin) → r' = r →
      stepF .stateTy (st.withTy r' (trRes t)) = some ([.armsStart], st.withTy r' (trRes t)) →
      ∃ (ts : List TyR) (res : TyR) (r : List Tok) (n' : Nat), n' < m + 1 + 0 + 1 ∧ r.length < st.toks.length ∧
      (∀ f, 2 * st.toks.length + 3 ≤ f → pArrows f st.toks = some (ts ++ [res], r)) ∧
      (∀ t ∈ ts, trRes t ≠ .nt ∧ (trRes t).nnt = true) ∧ (trRes res).nnt = true ∧ (ts = [] → st.cur.params.length ≠ 1) ∧
      StarN n' (.armsStart :: ks, { st with toks := r, ty := some (trRes res), cur := (ts.map trRes).foldl stAdd st.cur })
        ([], fin) ∧
      Star (.tyAtom :: .stateTy :: ks, st)
        (.armsStart :: ks, { st with toks := r, ty := some (trRes res), cur := (ts.map trRes).foldl stAdd st.cur }) := by
    intro r' hnot hp h2 e hstep; subst e
    refine ⟨[], t, r', m, by omega, hlt, fun f hf => ?_, by simp, hnnt, fun _ => hp, by simpa [St.withTy] using h2,
      by simpa [St.withTy] using hT.trans (Star.one (fs := ks) hstep)⟩
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
      obtain ⟨ts, res, r2, n', hn', h'⟩ := hfin [] (by simp) hp (by simpa using h2) rfl hs0
      exact ⟨ts, res, r2, n', by omega, h'⟩
  | cons tk r1 =>
    by_cases h17 : tk = .k 17
    · subst h17
      simp only [stepF, St.withTy] at hs
      by_cases hw : trRes t = .nt
      · simp [hw] at hs
      · by_cases hcap : 2 ^ 20 ≤ (if (trRes t == Sh.ls && !hasLs (List.map some st.cur.params)) = true then st.cur.npw
            else st.cur.npw + (trRes t).width)
        · simp only [hw, hcap, ↓reduceIte, if_false] at hs; cases hs
        simp only [hw, hcap, ↓reduceIte, if_false, Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨ts, res, r2, n', hn', hlt2, hp2, hts, hres, hnil, h3, hT3⟩ := ih m (by omega) h2
        refine ⟨t :: ts, res, r2, n', by omega, by simp at hlt2 hlt ⊢; omega, fun f hf => ?_, ?_, hres, by simp, ?_, ?_⟩
        · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
          rw [pArrows_succ, hpTy g (by omega)]
          simp only [Option.bind_some]
          rw [hp2 g (by simp at hlt hf ⊢; omega)]; rfl
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact ⟨hw, hnnt⟩
          · exact hts u hu
        · simpa [stAdd] using h3
        · have := (hT.trans (Star.one (fs := ks) hs0)).trans hT3
          simpa [stAdd, St.withTy] using this
    · have hnot : ∀ r', (tk :: r1) ≠ .k 17 :: r' := by intro r' e; cases e; exact h17 rfl
      have hs' : stepF .stateTy (st.withTy (tk :: r1) (trRes t)) =
          if st.cur.params.length = 1 then none else some ([.armsStart], st.withTy (tk :: r1) (trRes t)) := by
        simp only [stepF, St.withTy]
      rw [hs'] at hs
      by_cases hp : st.cur.params.length = 1
      · simp [hp] at hs
      · simp only [hp, if_false, Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨ts, res, r2, n', hn', h'⟩ := hfin _ hnot hp (by simpa using h2) rfl (by rw [hs']; simp [hp])
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
        StarN n' (armK stp ++ ks, { st with toks := r, binds := st.binds ++ env.map toBd, sslot := sl }) ([], fin) ∧
        Star (.armBind stp (c + 1) :: ks, st) (armK stp ++ ks, { st with toks := r, binds := st.binds ++ env.map toBd, sslot := sl }) := by
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
    obtain ⟨names, env, r', n', sl, hn', hpat, henv, hfr, hnd, hlt', h2, hT2⟩ :=
      ih m (by omega) (by exact hP) hc1 h1
    simp only at hpat henv hfr hlt' h2 hT2
    rw [hsl] at henv
    refine ⟨x :: names, (x, st.sslot, ps[c]) :: env, r', n', sl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · have := (Star.one (fs := ks) hs).trans hT2
      rw [hbd] at this; simpa using this
  · -- the last binder
    have hc1 : c + 1 = ps.length := by rw [hP] at hlt; simp at hlt; omega
    have hdrop : ps.drop c = [ps[c]] := by
      rw [List.drop_eq_getElem_cons hc, List.drop_eq_nil_of_le (by omega)]
    refine ⟨[x], [(x, st.sslot, ps[c])], r, m, st.sslot + ps[c].width, by omega, ?_, ?_, ?_, by simp, ?_, ?_, ?_⟩
    · rw [ht, armPat_bind, armPat]; rfl
    · rw [hdrop, mkEnv_cons, mkEnv]; rfl
    · intro y hy; simp at hy; subst hy; exact hb
    · rw [ht]; simp; omega
    · rw [hsl, hbd] at h1; simpa using h1
    · have := Star.one (fs := ks) hs
      rw [hsl, hbd] at this; simpa using this

/-- name resolution in an arm: the spec env (reversed `mkEnv`) is the machine's `toBd` bindings -/
theorem env_toBd (env : List (List Nat × Nat × Ps)) (h : ∀ e ∈ env, e.2.2 ≠ .fuel ∧ psCode e.2.2 ≠ .nt) (x : List Nat) :
    findEnv env.reverse x = (findB (env.map toBd) x).bind fun bd => (bdPs bd).map fun p => (bd.slot, p) := by
  unfold findEnv findB
  rw [← List.map_reverse, List.find?_map]
  have hf : ((fun b : Bd => b.name == x) ∘ toBd) = fun e => e.1 == x := by funext e; rfl
  rw [hf]
  cases hfd : env.reverse.find? (fun e => e.1 == x) with
  | none => rfl
  | some e =>
    have hm : e ∈ env := List.mem_reverse.mp (List.mem_of_find?_eq_some hfd)
    obtain ⟨h1, h2⟩ := h e hm
    have := bdPs_toBd h1 h2
    obtain ⟨y, sl, p⟩ := e
    simp only [Option.map_some, Option.bind_some, this]; rfl

theorem findB_toBd_isSome {env : List (List Nat × Nat × Ps)} {x : List Nat} {bd : Bd}
    (h : findB (env.map toBd) x = some bd) : ∃ e ∈ env, bd = toBd e := by
  unfold findB at h
  rw [← List.map_reverse, List.find?_map] at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨e, List.mem_reverse.mp (List.mem_of_find?_eq_some he), rfl⟩

/-- the fuel binder of a step arm (zeroDone, 77) -/
def nbBd (nb : List Nat) : Bd := ⟨nb, 0, some .nt, false⟩

theorem findB_cons_front (bd : Bd) (bs : List Bd) (x : List Nat) :
    findB (bd :: bs) x = match findB bs x with | some b => some b | none => if bd.name == x then some bd else none := by
  unfold findB
  simp only [List.reverse_cons, List.find?_append, List.find?_cons, List.find?_nil]
  cases bs.reverse.find? (fun b => b.name == x) <;> simp
  cases h : bd.name == x <;> simp_all

theorem findB_toBd_none {env : List (List Nat × Nat × Ps)} {x : List Nat} (h : ∀ e ∈ env, e.1 ≠ x) :
    findB (env.map toBd) x = none := by
  unfold findB
  rw [← List.map_reverse, List.find?_map]
  simp only [Option.map_eq_none_iff, List.find?_eq_none]
  intro e he; have := h e (List.mem_reverse.mp he); simpa [toBd] using this

/-- name resolution in a step arm: the fuel binder (innermost in the spec, outermost in the machine; names distinct) -/
theorem env_step (nb : List Nat) (env : List (List Nat × Nat × Ps)) (h : ∀ e ∈ env, e.2.2 ≠ .fuel ∧ psCode e.2.2 ≠ .nt)
    (hd : ∀ e ∈ env, e.1 ≠ nb) (x : List Nat) :
    findEnv ((nb, 0, .fuel) :: env.reverse) x =
      (findB (nbBd nb :: env.map toBd) x).bind fun bd => (bdPs bd).map fun p => (bd.slot, p) := by
  rw [findEnv_cons, findB_cons_front]
  by_cases hx : nb = x
  · subst hx
    rw [findB_toBd_none hd]; simp [nbBd, bdPs]
  · have : (nb == x) = false := by simpa using hx
    simp only [this, Bool.false_eq_true, if_false]
    rw [env_toBd env h x]
    cases findB (env.map toBd) x <;> simp [nbBd, this]

/-- the context of an arm (from the def-start context `hD` and the arm's name resolution `henv`) -/
theorem cxRel_arm {st0 st : St} {defs : List DefI} {E : List (List Nat × Nat × Ps)} {self : Option (List Nat × List Ps)}
    (hD : CxRel st0 ⟨defs, [], none⟩) (hd : st.defs = st0.defs)
    (htyped : ∀ x bd, findB st.binds x = some bd → bd.sh.isSome)
    (hinp : ∀ x bd, findB st.binds x = some bd → bd.inp = true → bd.sh = some .ls)
    (henv : ∀ x, findEnv E x = (findB st.binds x).bind fun bd => (bdPs bd).map fun p => (bd.slot, p))
    (hself : ∀ sn sps, self = some (sn, sps) → findDef defs sn = none)
    (harm : st.arm = true → ∃ sps, self = some (st.cur.name, sps) ∧ sps ≠ [] ∧
      sps.map psCode = st.cur.params.tail ∧
      (∀ (i : Nat) (h : i < sps.length), (sps[i] = .inp ↔ FirstLs st.cur.params.tail i)) ∧ ∀ p ∈ sps, p ≠ .sh .nt) :
    CxRel st ⟨defs, E, self⟩ :=
  ⟨htyped, hinp, henv, fun x => by rw [hd]; exact hD.defs x, fun x j di hx => by rw [hd]; exact hD.row x j di hx, hself, harm⟩

theorem toBd_typed {env : List (List Nat × Nat × Ps)} {pre : List Bd} (hpre : ∀ b ∈ pre, b.sh.isSome ∧ b.inp = false)
    {x : List Nat} {bd : Bd} (h : findB (pre ++ env.map toBd) x = some bd) : bd.sh.isSome ∧ (bd.inp = true → bd.sh = some .ls) := by
  unfold findB at h
  have hm := List.mem_reverse.mp (List.mem_of_find?_eq_some h)
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨h1, h2⟩ := hpre bd hm; exact ⟨h1, fun e => by rw [h2] at e; cases e⟩
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hm
    obtain ⟨y, sl, p⟩ := e
    refine ⟨rfl, fun hi => ?_⟩
    cases p <;> simp_all [toBd, psCode]

theorem eraseDups_of_nodup {α : Type} [BEq α] [LawfulBEq α] : ∀ {l : List α}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: as, h => by
    rw [List.eraseDups_cons]
    obtain ⟨ha, has⟩ := List.nodup_cons.mp h
    have hf : as.filter (fun b => !b == a) = as := by
      rw [List.filter_eq_self]; intro b hb; simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
      intro e; subst e; exact ha hb
    rw [hf, eraseDups_of_nodup has]

theorem armsStart_inv {st k st'} (h : stepF .armsStart st = some (k, st')) :
    st.ty ≠ some .nt ∧ ∃ r, st.toks = .k 18 :: .num 0 :: .k 15 :: r ∧ k = [.armBind false 1] ∧
      st' = { st with cur := { st.cur with res := st.ty }, nx := st.cur.npw, toks := r, sslot := 1 } := by
  simp only [stepF] at h
  split at h
  · cases h
  · rename_i hty
    refine ⟨hty, ?_⟩
    split at h
    · rename_i r ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨r, ht, rfl, rfl⟩
    · cases h

theorem zeroDone_inv {st k st'} (h : stepF .zeroDone st = some (k, st')) :
    ∃ z rest nb r, st.vals = z :: rest ∧ z.sh = st.cur.res ∧ st.toks = .k 18 :: .id nb :: .k 10 :: .num 1 :: .k 15 :: r ∧
      k = [.armBind true 1] ∧ st' = { st with toks := r, binds := [nbBd nb], arm := true, sslot := 1 } := by
  simp only [stepF] at h
  split at h
  · rename_i z rest hv
    split at h
    · rename_i hz
      split at h
      · rename_i nb r ht
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨z, rest, nb, r, hv, hz, ht, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

theorem mkLoop_inv {st k st'} (h : stepF .mkLoop st = some (k, st')) :
    ∃ s z rest, st.vals = s :: z :: rest ∧ s.sh = st.cur.res ∧ k = [] ∧
      st' = { st with vals := RN.mk 10 0 0 st.cur.res false [z, s] :: rest,
                      arena := st.arena ++ [RN.mk 10 0 0 st.cur.res false [z, s]] } := by
  simp only [stepF] at h
  split at h
  · rename_i s rest hv
    split at h
    · rename_i hs
      obtain ⟨st2, hm, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hl, rfl⟩ := mkNode_inv hm
      rw [hv] at hl ⊢
      match rest, hl with
      | z :: rest, _ => exact ⟨s, z, rest, rfl, hs, rfl, by simp⟩
    · cases h
  · cases h

theorem pArrows_noLs : ∀ f ts l r, pArrows f ts = some (l, r) → ∀ t ∈ l, t ≠ .sh .ls := by
  intro f
  induction f with
  | zero => intro ts l r h; simp [pArrows] at h
  | succ f ih =>
    intro ts l r h t ht
    rw [pArrows_succ] at h
    obtain ⟨⟨t0, r0⟩, h0, h1⟩ := Option.bind_eq_some_iff.mp h
    have hn0 := (pTy_noLs f).2 ts t0 r0 h0
    simp only at h1
    split at h1
    · obtain ⟨⟨l', r'⟩, h2, h3⟩ := Option.map_eq_some_iff.mp h1
      simp only [Prod.mk.injEq] at h3; obtain ⟨rfl, rfl⟩ := h3
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hn0
      · exact ih _ _ _ h2 t ht
    · simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
      simp at ht; subst ht; exact hn0

theorem sk_codes : ∀ (u : Bool) (ts : List TyR), (stateKinds u ts).map psCode = ts.map trRes
  | _, [] => rfl
  | u, t :: ts => by
    simp only [stateKinds, List.map_cons, sk_codes _ ts]
    congr 1
    cases t with
    | sh s => rfl
    | lst => cases u <;> rfl

theorem sk_nofuel : ∀ (u : Bool) (ts : List TyR), ∀ p ∈ stateKinds u ts, p ≠ .fuel
  | _, [], p, h => by simp [stateKinds] at h
  | u, t :: ts, p, h => by
    simp only [stateKinds, List.mem_cons] at h
    rcases h with rfl | h
    · cases t with
      | sh s => simp [pickPs]
      | lst => cases u <;> simp [pickPs]
    · exact sk_nofuel _ ts p h

theorem sk_nont (u : Bool) (ts : List TyR) (h : ∀ t ∈ ts, trRes t ≠ .nt) : ∀ p ∈ stateKinds u ts, p ≠ .sh .nt := by
  intro p hp e; subst e
  have : Sh.nt ∈ (stateKinds u ts).map psCode := List.mem_map.mpr ⟨_, hp, rfl⟩
  rw [sk_codes] at this
  obtain ⟨t, ht, e⟩ := List.mem_map.mp this
  exact h t ht e

theorem foldl_add_gen (l : List Nat) (a : Nat) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons, List.sum_cons]; rw [ih]; omega

theorem foldl_add_eq_sum (l : List Nat) : l.foldl (· + ·) 0 = l.sum := by
  rw [foldl_add_gen]; simp

theorem mkEnv_mem : ∀ (s : Nat) (ps : List Ps) (ns : List (List Nat)) (env : List (List Nat × Nat × Ps)),
    mkEnv s ps ns = some env → ∀ e ∈ env, e.2.2 ∈ ps ∧ e.1 ∈ ns
  | _, [], [], env, h => by simp [mkEnv] at h; subst h; simp
  | _, [], _ :: _, _, h => by simp [mkEnv] at h
  | _, _ :: _, [], _, h => by simp [mkEnv] at h
  | s, p :: ps, x :: ns, env, h => by
    rw [mkEnv_cons] at h
    obtain ⟨e', h1, rfl⟩ := Option.map_eq_some_iff.mp h
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · obtain ⟨a, b⟩ := mkEnv_mem _ ps ns e' h1 e he; exact ⟨by simp [a], by simp [b]⟩

theorem tyOk_of {v : RN} {t : Ty} {s : Sh} (h : TyRel v t) (hb : t ≠ .bot) (hi : v.isInp = false) (hs : v.sh = some s) :
    tyOk s t = true := by
  cases t with
  | s s' => rw [h.1] at hs; cases hs; simp [tyOk]
  | lit => rw [h.1] at hs; cases hs; rfl
  | inp => rw [h.1] at hi; cases hi
  | bot => exact absurd rfl hb

theorem join_s_of {v : RN} {t : Ty} {s : Sh} (h : TyRel v t) (hi : v.isInp = false) (hs : v.sh = some s) :
    ∃ x, t.join (.s s) = some (.s x) := by
  cases t with
  | s s' => rw [h.1] at hs; cases hs; exact ⟨s, by simp [Ty.join]⟩
  | lit => rw [h.1] at hs; cases hs; exact ⟨.uw, rfl⟩
  | inp => rw [h.1] at hi; cases hi
  | bot => exact ⟨s, rfl⟩

theorem loopNode_toNd {sh : Option Sh} {z s : RN} (hz : z.isInp = false) (hs : s.isInp = false) :
    (RN.mk 10 0 0 sh false [z, s]).toNd = .loop z.toNd s.toNd := by
  rw [RN.toNd_mk]; simp [RN.toNdL, hz, hs]

theorem pTy_nat (f : Nat) (r : List Tok) : pTy (f + 2) (.k 35 :: .k 17 :: r) = some (.sh .nt, .k 17 :: r) := by
  simp [pTy, pTyAtom]

/-- **fuel-loop def** (61/73/74/75/76/1/77/76/1/79): from `def name :` (at `Nat →`) to `defEnd` -/
theorem loop_spec {n : Nat} {ks : List Frame} {st fin : St} {defs : List DefI} {name : List Nat} {r : List Tok}
    (h : StarN n (.tyAtom :: .afterColon :: ks, st) ([], fin)) (ht : st.toks = .k 35 :: .k 17 :: r)
    (hcur : st.cur = DefR.fresh name) (hb : st.binds = []) (hv : st.vals = []) (harm : st.arm = false)
    (hD : CxRel st ⟨defs, [], none⟩) (hnn : ∀ d ∈ st.defs, ShNN d.res ∧ ∀ p ∈ d.params, p.nnt = true)
    (hfresh : findDef defs name = none) :
    ∃ lp st' n', n' < n ∧ StarN n' (.defEnd :: ks, st') ([], fin) ∧
      Star (.tyAtom :: .afterColon :: ks, st) (.defEnd :: ks, st') ∧ st'.vals = [lp] ∧ st'.defs = st.defs ∧
      st'.out = st.out ∧ st'.all = st.all ∧ st'.cur.name = name ∧ st'.cur.loop = true ∧ st'.toks.length < st.toks.length ∧
      (VT (rows st') lp → st'.nx < 2 ^ 20 → cw st'.cur.res < 2 ^ 20 →
        ∃ di : DefI, di.name = name ∧ di.params.map psCode = st'.cur.params ∧ st'.cur.res = some di.res ∧
          di.npw = st'.cur.npw ∧ (∀ (i : Nat) (h : i < di.params.length), (di.params[i] = .inp ↔ FirstLs st'.cur.params i)) ∧
          (∀ p ∈ di.params, p ≠ .sh .nt) ∧ (di.res.nnt = true ∧ ∀ p ∈ st'.cur.params, p.nnt = true) ∧
          ∀ f, 4 * st.toks.length + 8 ≤ f → pDef f defs (.k 1 :: .id name :: .k 8 :: st.toks) =
            some (di, { id := defs.length, npw := st'.cur.npw, nslots := st'.nx, kind := 1, nres := di.res.width,
                        body := lp.toNd }, st'.toks)) := by
  -- the `Nat` type and `→`
  obtain ⟨t0, r0, n1, hn1, hlt0, hp0, hT0, h1, _⟩ := ty_star h
  have ht0 : t0 = .sh .nt ∧ r0 = .k 17 :: r := by
    have := hp0 (2 * st.toks.length + 2) (Nat.le_refl _)
    rw [ht, show 2 * (Tok.k 35 :: Tok.k 17 :: r).length + 2 = (2 * r.length + 4) + 2 by simp; omega, pTy_nat] at this
    cases this; exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := ht0
  match n1, h1 with
  | 0, h1 => exact absurd h1.zero_nil.1 (by simp)
  | m1 + 1, h1 =>
  obtain ⟨k1, st1, hs1, h2⟩ := h1.head
  have hs1' := hs1
  simp only [stepF, St.withTy, trRes] at hs1
  simp at hs1
  obtain ⟨_, rfl, rfl⟩ := hs1
  have Tp1 := hT0.trans (Star.one (fs := ks) hs1')
  simp only [List.cons_append, List.nil_append] at h2 Tp1
  -- the state types
  obtain ⟨ts, res, r1, n2, hn2, hlt1, hpA, hts, hres, hnil, h3, hTA⟩ := arrows_spec m1 h2
  simp only at hlt1 hpA hnil h3 hTA
  have Tp2 := Tp1.trans hTA
  have hls : ∀ t ∈ ts, t ≠ .sh .ls := fun t ht =>
    pArrows_noLs _ _ _ _ (hpA _ (Nat.le_refl _)) t (List.mem_append_left _ ht)
  have hp1 : (st.cur.params ++ [Sh.nt]) = [Sh.nt] := by rw [hcur]; rfl
  have hne : ts ≠ [] := fun e => hnil e (by rw [hp1]; rfl)
  obtain ⟨hfp, hfn, hfname, hfres, hfloop⟩ := fold_stAdd ts hls
    { st.cur with npw := 1, loop := true, params := st.cur.params ++ [.nt], nni := st.cur.nni + 1 }
  have hu0 : hasLs ((st.cur.params ++ [Sh.nt]).map some) = false := by rw [hp1]; rfl
  rw [hu0] at hfp hfn
  have hP : ((ts.map trRes).foldl stAdd
      { st.cur with npw := 1, loop := true, params := st.cur.params ++ [.nt], nni := st.cur.nni + 1 }).params =
      .nt :: (stateKinds false ts).map psCode := by rw [hfp, hp1]; rfl
  -- armsStart
  match n2, h3 with
  | 0, h3 => exact absurd h3.zero_nil.1 (by simp)
  | m2 + 1, h3 =>
  obtain ⟨k3, st3, hs3, h4⟩ := h3.head
  obtain ⟨hty, r2, hr1, rfl, rfl⟩ := armsStart_inv hs3
  have Tp3 := Tp2.trans (Star.one (fs := ks) hs3)
  simp only at hty hr1
  simp only [List.cons_append, List.nil_append] at h4 Tp3
  -- the zero arm's binders
  have hcodes : (stateKinds false ts).map psCode = ts.map trRes := sk_codes false ts
  have hfuel := sk_nofuel false ts
  have hinp : ∀ (i : Nat) (h : i < (stateKinds false ts).length),
      ((stateKinds false ts)[i] = .inp ↔ FirstLs ((stateKinds false ts).map psCode) i) := by
    intro i h; rw [hcodes, stateKinds_inp ts hls false i h]; simp
  have hpsl : 0 < (stateKinds false ts).length := by
    rw [stateKinds_length]; exact List.length_pos_iff.mpr hne
  obtain ⟨zn, envZ, r3, n4, sl, hn4, hpatZ, henvZ, hfrZ, hndZ, hlt3, h5, hTZ⟩ :=
    armBind_spec (stateKinds false ts) hfuel hinp m2 (c := 0) (by exact hP) hpsl h4
  simp only [List.drop_zero, armK, List.cons_append, List.nil_append] at hpatZ henvZ hfrZ hlt3 h5 hTZ
  have Tp4 := Tp3.trans hTZ
  generalize hC : (List.map trRes ts).foldl stAdd
    { st.cur with npw := 1, loop := true, params := st.cur.params ++ [.nt], nni := st.cur.nni + 1 } = C at h5 hP hfp hfn hfname hfres hfloop Tp4
  obtain ⟨S3, hb3, hd3, hc3, ha3, ht3, hn3, hv3, ho3, hal3, h5, Tp4⟩ : ∃ S3 : St, S3.binds = envZ.map toBd ∧ S3.defs = st.defs ∧
      S3.cur = { C with res := some (trRes res) } ∧ S3.arm = false ∧ S3.toks = r3 ∧ S3.nx = C.npw ∧ S3.vals = [] ∧
      S3.out = st.out ∧ S3.all = st.all ∧ StarN n4 (.expr 0 0 :: .zeroDone :: ks, S3) ([], fin) ∧
      Star (.tyAtom :: .afterColon :: ks, st) (.expr 0 0 :: .zeroDone :: ks, S3) :=
    ⟨{ st with toks := r3, nx := C.npw, binds := st.binds ++ envZ.map toBd, cur := { C with res := some (trRes res) }, ty := some (trRes res), sslot := sl }, by simp [hb], rfl, rfl, harm, rfl, rfl, hv, rfl, rfl, h5, Tp4⟩
  -- the zero arm's context
  have hpsP : ∀ p ∈ stateKinds false ts, p ≠ .fuel ∧ psCode p ≠ .nt ∧ (psCode p).nnt = true := by
    intro p hp
    have hm : psCode p ∈ ts.map trRes := by rw [← hcodes]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨t, ht', e⟩ := List.mem_map.mp hm
    exact ⟨hfuel p hp, by rw [← e]; exact (hts t ht').1, by rw [← e]; exact (hts t ht').2⟩
  have hZe : ∀ e ∈ envZ, e.2.2 ≠ .fuel ∧ psCode e.2.2 ≠ .nt := fun e he =>
    let h := hpsP _ (mkEnv_mem _ _ _ _ henvZ e he).1; ⟨h.1, h.2.1⟩
  have hc0 : CxRel S3 ⟨defs, envZ.reverse, none⟩ := by
    refine cxRel_arm hD hd3 (fun x bd hx => ?_) (fun x bd hx => ?_) (fun x => ?_) (fun _ _ h => by cases h) (fun h => ?_)
    · rw [hb3] at hx; exact (toBd_typed (pre := []) (by simp) (by simpa using hx)).1
    · rw [hb3] at hx; exact (toBd_typed (pre := []) (by simp) (by simpa using hx)).2
    · rw [hb3]; exact env_toBd envZ hZe x
    · rw [ha3] at h; cases h
  have hrows3 : rows S3 = st.defs ++ [{ C with res := some (trRes res) }] := by simp [rows, hd3, hc3]
  have hnn3 : CxNN S3 := by
    refine ⟨fun bd hbd => ?_, fun d hd => ?_⟩
    · rw [hb3] at hbd
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hbd
      obtain ⟨_, _, h3⟩ := hpsP _ (mkEnv_mem _ _ _ _ henvZ e he).1
      exact ⟨_, rfl, h3⟩
    · rw [hrows3] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hnn d hd
      · simp at hd; subst hd
        refine ⟨⟨_, rfl, hres⟩, fun p hp => ?_⟩
        simp only [hP, List.mem_cons] at hp
        rcases hp with rfl | hp
        · rfl
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact (hpsP q hq).2.2
  obtain ⟨z, S4, n5, hn5, hpo4, hlt4, h6, _, hsh4, hsp4, hTE0⟩ := expr_star (by decide) h5 hc0 hnn3
  have Tp5 := Tp4.trans hTE0
  -- zeroDone
  match n5, h6 with
  | 0, h6 => exact absurd h6.zero_nil.1 (by simp)
  | m5 + 1, h6 =>
  obtain ⟨k6, S5, hs6, h7⟩ := h6.head
  obtain ⟨z', rest, nb, r5, hv4, hz, ht4, rfl, rfl⟩ := zeroDone_inv hs6
  have Tp6 := Tp5.trans (Star.one (fs := ks) hs6)
  rw [hpo4.vals, hv3] at hv4; injection hv4 with e1 e2; subst e1 e2
  simp only [List.cons_append, List.nil_append] at h7
  have hcur4 : S4.cur = { C with res := some (trRes res) } := by rw [hpo4.cur, hc3]
  -- the step arm's binders
  obtain ⟨sn, envS, r6, n7, sl2, hn7, hpatS, henvS, hfrS, hndS, hlt6, h8, hTS⟩ :=
    armBind_spec (stateKinds false ts) hfuel hinp m5 (c := 0) (by simp only; rw [hcur4]; exact hP) hpsl h7
  simp only [List.drop_zero, armK, List.cons_append, List.nil_append] at hpatS henvS hfrS hlt6 h8 hTS Tp6
  have Tp7 := Tp6.trans hTS
  obtain ⟨S6, hb6, hd6, hc6, ha6, ht6, hn6, hv6, ho6, hal6, h8, Tp7⟩ : ∃ S6 : St, S6.binds = nbBd nb :: envS.map toBd ∧ S6.defs = st.defs ∧
      S6.cur = { C with res := some (trRes res) } ∧ S6.arm = true ∧ S6.toks = r6 ∧ S6.nx = S4.nx ∧ S6.vals = [z] ∧
      S6.out = st.out ∧ S6.all = st.all ∧ StarN n7 (.expr 0 1 :: .mkLoop :: .defEnd :: ks, S6) ([], fin) ∧
      Star (.tyAtom :: .afterColon :: ks, st) (.expr 0 1 :: .mkLoop :: .defEnd :: ks, S6) :=
    ⟨{ S4 with toks := r6, binds := nbBd nb :: envS.map toBd, arm := true, sslot := sl2 }, rfl, by rw [hpo4.defs, hd3], hcur4, rfl, rfl, rfl, by simp [hpo4.vals, hv3], by simp [hpo4.out, ho3], by simp [hpo4.all, hal3], h8, by simpa using Tp7⟩
  -- the step arm's context
  have hSe : ∀ e ∈ envS, e.2.2 ≠ .fuel ∧ psCode e.2.2 ≠ .nt := fun e he =>
    let h := hpsP _ (mkEnv_mem _ _ _ _ henvS e he).1; ⟨h.1, h.2.1⟩
  have hSn : ∀ e ∈ envS, e.1 ≠ nb := by
    intro e he heq
    have := hfrS e.1 (mkEnv_mem _ _ _ _ henvS e he).2
    rw [heq] at this; simp [findB, nbBd] at this
  have hname : C.name = name := by rw [hfname, hcur]; rfl
  have hc1 : CxRel S6 ⟨defs, (nb, 0, .fuel) :: envS.reverse, some (name, stateKinds false ts)⟩ := by
    refine cxRel_arm hD hd6 (fun x bd hx => ?_) (fun x bd hx => ?_) (fun x => ?_) (fun sn sps h => ?_) (fun _ => ?_)
    · rw [hb6] at hx; exact (toBd_typed (pre := [nbBd nb]) (by simp [nbBd]) (by simpa using hx)).1
    · rw [hb6] at hx; exact (toBd_typed (pre := [nbBd nb]) (by simp [nbBd]) (by simpa using hx)).2
    · rw [hb6]; exact env_step nb envS hSe hSn x
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hfresh
    · refine ⟨stateKinds false ts, by rw [hc6]; simp [hname], fun e => by rw [e] at hpsl; simp at hpsl, ?_, ?_,
        sk_nont false ts (fun t ht => (hts t ht).1)⟩
      · rw [hc6]; simp [hP]
      · intro i hi; rw [hc6]; simp only [hP, List.tail_cons]; exact hinp i hi
  have hrows6 : rows S6 = rows S3 := by simp [rows, hd6, hc6, hd3, hc3]
  have hnn6 : CxNN S6 := by
    refine ⟨fun bd hbd => ?_, fun d hd => by rw [hrows6] at hd; exact hnn3.2 d hd⟩
    rw [hb6] at hbd
    rcases List.mem_cons.mp hbd with rfl | hbd
    · exact ⟨.nt, rfl, rfl⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hbd
      obtain ⟨_, _, h3⟩ := hpsP _ (mkEnv_mem _ _ _ _ henvS e he).1
      exact ⟨_, rfl, h3⟩
  obtain ⟨s', S7, n8, hn8, hpo7, hlt7, h9, _, hsh7, hsp7, hTE1⟩ := expr_star (by decide) h8 hc1 hnn6
  have Tp8 := Tp7.trans hTE1
  -- mkLoop
  match n8, h9 with
  | 0, h9 => exact absurd h9.zero_nil.1 (by simp)
  | m8 + 1, h9 =>
  obtain ⟨k10, S8, hs10, h10⟩ := h9.head
  obtain ⟨s'', z'', rest', hv7, hs7sh, rfl, rfl⟩ := mkLoop_inv hs10
  have Tp9 := Tp8.trans (Star.one (fs := .defEnd :: ks) hs10)
  rw [hpo7.vals, hv6] at hv7; injection hv7 with e1 e2; injection e2 with e3 e4; subst e1 e3 e4
  simp only [List.nil_append] at h10
  have hcur7 : S7.cur = { C with res := some (trRes res) } := by rw [hpo7.cur, hc6]
  have hCloop : C.loop = true := by rw [hfloop]
  have hl6 : r6.length < r5.length := hlt6
  have ht4' : S4.toks.length = r5.length + 5 := by rw [ht4]; simp
  have ht3' : S4.toks.length < r3.length := by rw [← ht3]; exact hlt4
  have hr1l : r1.length = r2.length + 3 := by rw [hr1]; simp
  have hrl : r.length + 2 = st.toks.length := by rw [ht]; simp
  refine ⟨_, _, m8, by omega, h10, by simpa using Tp9, rfl, by simp [hpo7.defs, hd6], by simp [hpo7.out, ho6], by simp [hpo7.all, hal6],
    by simp [hcur7, hname], by simp [hcur7, hCloop], ?_, fun hvt hcap1 hcap2 => ?_⟩
  · have := hlt7; simp only [ht6] at this; simp; omega
  -- the spec side
  have hvt' : VT (rows S3) (RN.mk 10 0 0 S7.cur.res false [z, s']) := by
    have e : rows S3 = S7.defs ++ [S7.cur] := by simp [rows, hpo7.defs, hpo7.cur, hd6, hc6, hd3, hc3]
    rw [e]; simpa [rows] using hvt
  have hnoi := nodeOK_noInp (by decide) hvt'.self
  have hzi : z.isInp = false := hnoi z (by simp)
  have hsi : s'.isInp = false := hnoi s' (by simp)
  obtain ⟨tz, htz, _, hpz⟩ := hsp4 (hvt'.kid (by simp))
  obtain ⟨tsx, htsx, _, hps⟩ := hsp7 (by rw [hrows6]; exact hvt'.kid (by simp))
  have hzs : z.sh = some (trRes res) := by rw [hz, hcur4]
  have hss : s'.sh = some (trRes res) := by rw [hs7sh, hcur7]
  refine ⟨{ name, params := .fuel :: stateKinds false ts, res := trRes res, resLst := false, npw := 1 + ((stateKinds false ts).map Ps.width).foldl (· + ·) 0 }, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun f hf => ?_⟩
  · simp [hcur7, hP, psCode]
  · simp [hcur7]
  · simp [hcur7, hfn, foldl_add_eq_sum]
  · intro i hi
    simp only [hcur7, hP]
    cases i with
    | zero => simp [FirstLs]
    | succ i =>
      rw [firstLs_cons_succ]
      simp only [List.getElem_cons_succ]
      rw [hinp i (by simpa using hi)]; simp
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · exact sk_nont false ts (fun t ht => (hts t ht).1) p hp
  · refine ⟨hres, fun q hq => ?_⟩
    simp only [hcur7, hP, List.mem_cons] at hq
    rcases hq with rfl | hq
    · rfl
    · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hq; exact (hpsP p' hp').2.2
  · have hA := hpA f (by omega)
    have hZ := hpz f (by rw [ht3]; omega)
    rw [ht3, hn3] at hZ
    have hS := hps f (by rw [ht6]; omega)
    rw [ht6, hn6] at hS
    rw [ht]
    simp only [pDef, hfresh, Option.isSome_none, Bool.false_eq_true, if_false, hA, Option.bind_some, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.reverse_reverse]
    have hN1 : (trRes res).hasN = false := Sh.hasN_of_nnt hres (fun e => hty (by rw [e]))
    have hN2 : ∀ p ∈ stateKinds false ts, (match p with | Ps.sh s => s.hasN | _ => false) = false := by
      intro p hp
      have := hpsP p hp
      cases p with
      | sh s' => exact Sh.hasN_of_nnt this.2.2 this.2.1
      | _ => rfl
    have hnpw : C.npw = 1 + List.foldl (fun x1 x2 => x1 + x2) 0 (List.map Ps.width (stateKinds false ts)) := by
      rw [hfn, foldl_add_eq_sum]
    rw [hnpw] at hZ
    simp only [show ((0 : Nat) == 1) = false from rfl] at hZ
    simp only [show ((1 : Nat) == 1) = true from rfl] at hS
    have hedZ : zn.eraseDups.length = zn.length := by rw [eraseDups_of_nodup hndZ]
    have hndS' : (nb :: sn).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hx => ?_, hndS⟩
      have := hfrS nb hx; simp [findB, nbBd] at this
    have hedS : (nb :: sn).eraseDups.length = sn.length + 1 := by rw [eraseDups_of_nodup hndS']; rfl
    have htz0 : tyOk (trRes res) tz = true := tyOk_of htz ((nobot f).1 _ _ _ _ hZ) hzi hzs
    obtain ⟨xj, hxj⟩ := join_s_of htsx hsi hss
    simp only [hr1, hpatZ, Option.bind_some, hedZ, bne_self_eq_false, henvZ, hZ, htz0, Bool.not_true, ht4, hpatS, hedS,
      henvS, hS, hxj, Bool.false_eq_true, if_false]
    split
    · rename_i hcond
      exfalso
      rw [hN1, Bool.false_or, List.any_eq_true] at hcond
      obtain ⟨p, hp, hpt⟩ := hcond
      have := hpsP p hp
      cases p with
      | sh s' =>
        have e : s'.hasN = false := Sh.hasN_of_nnt this.2.2 this.2.1
        simp only at hpt; rw [e] at hpt; cases hpt
      | _ => simp at hpt
    · rw [hcur7, loopNode_toNd hzi hsi]
      have hw20 : (trRes res).width < 2 ^ 20 := by have := hcap2; rw [hcur7] at this; simpa [cw] using this
      have hn20 : S7.nx < 2 ^ 20 := by simpa using hcap1
      simp only [hnpw, show ¬ (2 ^ 20 ≤ S7.nx ∨ 2 ^ 20 ≤ (trRes res).width) by omega, if_false]

end ParRun
