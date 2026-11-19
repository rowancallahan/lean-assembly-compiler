/- Nano/V2Self/Proof/ParRunHCall: the call-like heads of a primary (box G, for box B's `HCall`): a call of a FINISHED def and a
prim application reflect ParSpec's `pApp`, given the expression refinement for shorter runs.
`AtomV` / `atomV_run`: an argument-atom segment (leaf, or parenthesised via `prim_paren`) with the spec equation under `VT`. -/
import Nano.V2Self.Proof.ParRunPrimS
import Nano.V2Self.Proof.ParRunCallSpec
import Nano.V2Self.Proof.ParSpecLen
namespace ParRun
open ParSpec

/-- an argument atom: one value pushed; if it is validated, it is `pAtom` (non-tail) at every fuel ≥ 4·|toks| + 1 -/
def AtomV (cx : Cx) (st st' : St) : Prop :=
  ∃ v, Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧
      ∀ f, 4 * st.toks.length + 1 ≤ f → pAtom f cx false st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx))

theorem atomV_run {n : Nat} (hE : ∀ n' < n, ExprSpec n') {st st' : St} {cx : Cx}
    (h : StarN n ([.argAtom], st) ([], st')) (hc : CxRel st cx) (hnn : CxNN st) : AtomV cx st st' := by
  rcases atom_run h with ⟨r, n', ht, rfl, hrun⟩ | ⟨st1, n', _, hl, hrun⟩
  · obtain ⟨v, st2, n2, _, hpost, hltk, hr2, hsh, hsp⟩ :=
      prim_paren (n := n') (md := 0) (ks := []) (fun k hk => hE k (by omega)) hc hnn ht (by simpa [bm] using hrun)
    obtain ⟨_, he⟩ := hr2.nil_inv
    cases he
    refine ⟨v, hpost, hltk, hsh, fun hvt => ?_⟩
    obtain ⟨ty, hty, _, hp⟩ := hsp hvt
    refine ⟨ty, hty, fun f hf => ?_⟩
    have := hp (f + 1) (by omega)
    rw [ht, pApp_paren] at this
    rw [ht]; simpa using this
  · obtain ⟨_, he⟩ := hrun.nil_inv
    cases he
    obtain ⟨r, v, hlt, hk, hp, hst⟩ := hl.eff
    refine ⟨v, ?_, by rw [hst]; exact hlt, ?_, fun _ => ?_⟩
    · rw [hst]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp; omega, Nat.le_refl _⟩
    · cases hl with
      | num ht => simp [leaf] at hst; obtain ⟨_, rfl, _⟩ := hst; exact ⟨.uw, rfl, rfl⟩
      | nil ht => simp [leaf] at hst; obtain ⟨_, rfl, _⟩ := hst; exact ⟨.ls, rfl, rfl⟩
      | bnew ht => simp [leaf] at hst; obtain ⟨_, rfl, _⟩ := hst; exact ⟨.bf, rfl, rfl⟩
      | loc ht hbd hlo =>
        unfold locOf at hlo; split at hlo
        · cases hlo
        · simp at hlo; subst hlo; simp at hst; obtain ⟨_, rfl, _⟩ := hst
          exact hnn.1 _ (findB_mem' hbd)
      | cst ht hbd hd hj hpar hm =>
        obtain ⟨_, rfl⟩ := mkNode_inv hm; simp at hst; obtain ⟨_, rfl, _⟩ := hst
        exact (hnn.2 _ (defs_sub_rows (List.mem_of_getElem? hj))).1
    · obtain ⟨v', ty, r', hst', hty, _, hf⟩ := atomLeaf_spec hc hl false st.nx
      rw [hst] at hst'
      have hv : v' = v := by
        have := congrArg St.vals hst'; simp at this; exact this.symm
      have hr : r' = r := by
        have := congrArg St.toks hst'; simp at this; exact this.symm
      subst hv hr
      refine ⟨ty, hty, fun f hf' => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [hst]; exact hf g

/-- `tyMatch` from Par1's argument check, with the type facts read off the spec (not `bot`, `len'` is Nat) -/
theorem tyMatch_of2 {p : Ps} {v : RN} {ty : Ty} (hty : TyRel v ty) (hnb : ty ≠ .bot) (hlen : v.tag = 9 → v.a = 1 → ty = .s .nt)
    (hn : p ≠ .sh .nt) (hi : p = .inp ↔ v.isInp = true)
    (hok : v.sh = some (psCode p) ∨ (psCode p = .nt ∧ (v.tag = 1 ∨ (v.tag = 9 ∧ v.a = 1)))) : tyMatch p ty = true := by
  cases ty with
  | bot => exact absurd rfl hnb
  | inp =>
    obtain ⟨hin, _⟩ := hty
    have := hi.mpr hin; subst this; rfl
  | lit =>
    obtain ⟨huw, hni⟩ := hty
    cases p with
    | inp => have := hi.mp rfl; rw [hni] at this; cases this
    | fuel => rfl
    | sh s =>
      rcases hok with h | ⟨h1, _⟩
      · rw [huw] at h; simp [psCode] at h; subst h; rfl
      · exact absurd (by simpa [psCode] using h1) hn
  | s t =>
    obtain ⟨hs, hni, ht1⟩ := hty
    cases p with
    | inp => have := hi.mp rfl; rw [hni] at this; cases this
    | fuel =>
      rcases hok with h | ⟨_, h2 | ⟨h2, h3⟩⟩
      · rw [hs] at h; simp [psCode] at h; subst h; rfl
      · exact absurd h2 ht1
      · have := hlen h2 h3; cases this; rfl
    | sh s =>
      rcases hok with h | ⟨h1, _⟩
      · rw [hs] at h; simp [psCode] at h; subst h; simp [tyMatch]
      · exact absurd (by simpa [psCode] using h1) hn

/-- the two type facts a non-tail atom parse gives -/
theorem atom_facts {f : Nat} {cx : Cx} {ts : List Tok} {nx nx' : Nat} {v : RN} {ty : Ty} {r : List Tok}
    (h : pAtom f cx false ts nx = some (v.toNd, ty, r, nx')) : ty ≠ .bot ∧ (v.tag = 9 → v.a = 1 → ty = .s .nt) := by
  refine ⟨(nobot f).2.2.2 _ _ _ _ h, fun h9 h1 => ?_⟩
  obtain ⟨t, a, b, sh, pe, ks⟩ := v
  simp only [RN.tag, RN.a] at h9 h1
  subst h9 h1
  exact (lenTy f).2.2.2 _ _ _ _ h _ (toNd_prim1 1 b sh pe ks (by decide))

theorem rows_eq {st st' : St} (hd : st'.defs = st.defs) (hc : st'.cur = st.cur) : rows st' = rows st := by
  simp [rows, hd, hc]

/-- `k` argument atoms: the values, and (under validation of all of them) `pArgs` for every matching parameter list -/
theorem argsV {N : Nat} (hE : ∀ n' < N, ExprSpec n') {cx : Cx} : ∀ {k m : Nat} {st st' : St}, Atoms k st st' m → m ≤ N →
    CxRel st cx → CxNN st →
    ∃ vs : List RN, vs.length = k ∧ st'.vals = vs.reverse ++ st.vals ∧ st'.binds = st.binds ∧ st'.defs = st.defs ∧ st'.cur = st.cur ∧
      st'.arm = st.arm ∧ st'.all = st.all ∧ st'.toks.length ≤ st.toks.length ∧ st.nx ≤ st'.nx ∧ (∀ v ∈ vs, ShNN v.sh) ∧
      ((∀ v ∈ vs, VT (rows st) v) → ∃ vts : List (RN × Ty), vts.map (·.1) = vs ∧
        (∀ p ∈ vts, TyRel p.1 p.2 ∧ p.2 ≠ .bot ∧ (p.1.tag = 9 → p.1.a = 1 → p.2 = .s .nt)) ∧
        ∀ ps, ArgsMatch ps vts → ∀ f, 4 * st.toks.length + 2 ≤ f →
          pArgs f cx ps st.toks st.nx = some (vts.map (fun p => (p.1.toNd, p.2)), st'.toks, st'.nx)) := by
  intro k m st st' h
  induction h with
  | nil st =>
    intro _ _ _
    refine ⟨[], rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun v hv => absurd hv (by simp), fun _ => ?_⟩
    refine ⟨[], rfl, fun p hp => absurd hp (by simp), fun ps hps f hf => ?_⟩
    cases hps
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact pArgs_nil g cx _ _
  | @cons k st st1 st2 n1 n2 ha _ ih =>
    intro hm hc hnn
    obtain ⟨v, hpo, hlt, hsh, hsp⟩ := atomV_run (fun k hk => hE k (by omega)) ha hc hnn
    have hc1 := CxRel.transport hc hpo.binds hpo.defs
    have hnn1 := CxNN.transport hnn hpo.binds hpo.defs hpo.cur
    obtain ⟨vs, hlen, hvals, hb, hd, hcu, harm, hall, htk, hnx, hshs, hsps⟩ := ih (by omega) hc1 hnn1
    have hrows := rows_eq hpo.defs hpo.cur
    refine ⟨v :: vs, by simp [hlen], by rw [hvals, hpo.vals]; simp, hb.trans hpo.binds, hd.trans hpo.defs, hcu.trans hpo.cur,
      harm.trans hpo.arm, hall.trans hpo.all, by omega, Nat.le_trans hpo.nx hnx, ?_, fun hvt => ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hsh
      · exact hshs u hu
    · obtain ⟨ty, hty, hpa⟩ := hsp (hvt v (by simp))
      obtain ⟨vts, hmap, hfacts, hpargs⟩ := hsps (fun u hu => by rw [hrows]; exact hvt u (by simp [hu]))
      have hf0 := atom_facts (hpa _ (Nat.le_refl _))
      refine ⟨(v, ty) :: vts, by simp [hmap], ?_, fun ps hps f hf => ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨hty, hf0.1, hf0.2⟩
        · exact hfacts p hp
      · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        cases hps with
        | cons hm1 hrest =>
          rw [pArgs_cons, hpa g (by omega)]
          simp only [Option.bind_some, hm1, if_true]
          rw [hpargs _ hrest g (by omega)]
          rfl

theorem primRes_nnt (p : Nat) : (primRes p).nnt = true := by
  unfold primRes; split <;> (try split) <;> (try split) <;> rfl

theorem VT.kids {ds : List DefR} {t a b : Nat} {sh : Option Sh} {pe : Bool} {ks : List RN} (h : VT ds (.mk t a b sh pe ks)) :
    ∀ v ∈ ks, VT ds v := fun _ hv u hu => h u (kid_nodes_sub hv hu)

/-- **prim application** (B's `HCall`, prim-token case) -/
theorem hcall_prim {n : Nat} (hE : ∀ n' < n, ExprSpec n') {md : Nat} {ks : List Frame} {st fin : St} {cx : Cx} {t : Nat} {r : List Tok}
    (h : StarN n (.prim md :: ks, st) ([], fin)) (hc : CxRel st cx) (hnn : CxNN st) (ht : st.toks = .k t :: r) (h1 : 38 < t)
    (h2 : t < 48) : PrimConcl n md ks st fin cx := by
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n0 + 1, h =>
  obtain ⟨k, st0, hs, hrun⟩ := h.head
  rw [prim_head ht h1 h2] at hs; cases hs
  obtain ⟨ps, hsig, hpl, hcode, hinpi, hnf⟩ := prim_sig h1 h2
  have hrun' : StarN n0 (.args (.pr (t - 38)) (primAr (t - 38)) :: .mkCallN (.pr (t - 38)) st.vals.length :: ks,
      { st with toks := r }) ([], fin) := hrun
  obtain ⟨st1, m, n1, hat, rfl, hk⟩ := args_run _ hrun'
  obtain ⟨vs, hlen, hvals, hb, hd, hcu, harm, hall', htk, hnx, hshs, hsps⟩ :=
    argsV (N := m + n1 + primAr (t - 38) + 1) (fun k hk => hE k (by omega)) hat (by omega)
      (CxRel.transport hc rfl rfl) (CxNN.transport hnn rfl rfl rfl)
  obtain ⟨hall, nd, n', hnode, heq, hfin⟩ :=
    call_tail (c := .pr (t - 38)) (as := vs.reverse) (base := st.vals) hvals rfl hk
  simp only [List.length_reverse, List.reverse_reverse, callNode, Option.some.injEq] at hnode heq hall
  subst hnode
  refine ⟨RN.mk 9 (t - 38) 0 (some (primRes (t - 38))) false vs,
    { st1 with vals := RN.mk 9 (t - 38) 0 (some (primRes (t - 38))) false vs :: st.vals,
               arena := st1.arena ++ [RN.mk 9 (t - 38) 0 (some (primRes (t - 38))) false vs] },
    n', by omega, ⟨rfl, hb, hd, hcu, harm, hall', by rw [ht]; simp at htk ⊢; omega, hnx⟩,
    by rw [ht]; simp at htk ⊢; omega, hfin, ⟨_, rfl, primRes_nnt _⟩, fun hvt => ?_⟩
  obtain ⟨vts, hmap, hfacts, hpargs⟩ := hsps hvt.kids
  have hlv : vts.length = vs.length := by rw [← hmap]; simp
  have hinp : InpPair ps vs := prim_inpPair h1 h2 hsig (by omega) hvt.self
  have hm : ArgsMatch ps vts := by
    refine argsMatch_of _ _ (by omega) fun idx i1 i2 => ?_
    have i3 : idx < vs.length := by omega
    obtain ⟨v, w, hv, hw, hcond⟩ := hall (vs.length - 1 - idx) (by omega)
    have e1 := operand_idx vs st.vals idx i3
    rw [hvals, e1] at hv; cases hv
    have e2 : arity st1 (.pr (t - 38)) - (vs.length - 1 - idx + 1) = idx := by
      have : arity st1 (.pr (t - 38)) = primAr (t - 38) := rfl
      rw [this]; omega
    rw [e2] at hw
    have hc1 := hcode idx i1
    rw [List.getElem?_eq_getElem i1] at hc1
    simp only [Option.map_some, Option.some.injEq] at hc1
    have e3 : w = psCode ps[idx] := by
      simp only [parCode, Option.some.injEq] at hw; rw [hc1]; exact hw.symm
    subst e3
    have hne : ps[idx] ≠ .sh .nt := fun e => primPar_ne_nt (t - 38) idx (by rw [← hc1, e]; rfl)
    have hvi : (vts[idx]).1 = vs[idx] := by
      have := congrArg (fun l => l[idx]?) hmap
      simpa [List.getElem?_eq_getElem i2, List.getElem?_eq_getElem i3] using this
    obtain ⟨f1, f2, f3⟩ := hfacts _ (List.getElem_mem i2)
    rw [hvi] at f1 f3
    exact tyMatch_of2 f1 f2 f3 hne (by have := hinp.get idx i1 i3; simpa using this) hcond
  have h4 : t - 38 < 4 → ps.head? = some .inp := by
    intro h; have := (hinpi 0).mpr ⟨rfl, h⟩
    cases ps with
    | nil => simp at this
    | cons q qs => simpa using this
  have htn := prim_toNd (p := t - 38) (sh := some (primRes (t - 38))) hinp h4
  refine ⟨.s (primRes (t - 38)), ⟨rfl, rfl, by simp [RN.tag]⟩, fun hc' => by rw [htn] at hc'; simp [Nd.tailCont] at hc', fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [ht, pApp]
  simp only [hsig]
  rw [hpargs ps hm g (by rw [ht] at hf; simp at hf ⊢; omega)]
  simp only [Option.map_some, List.map_map]
  rw [htn, ← hmap]
  simp [Function.comp_def]

end ParRun
