/- Nano/V2Self/Proof/ParRunPrimS: the primary (task 3) ↔ ParSpec `pApp` (box B): leaf atoms (G's `atomLeaf_spec`),
parentheses and tuples; the call-like heads (def call, prim token, self-call) are the hypothesis `HCall`. -/
import Nano.V2Self.Proof.ParRunTup
namespace ParRun
open ParSpec

/-- the conclusion of `PrimSpec` -/
def PrimConcl (n md : Nat) (ks : List Frame) (st fin : St) (cx : Cx) : Prop :=
  ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ (v.toNd.tailCont = true → v.pend = true) ∧
      ∀ f, 4 * st.toks.length + 2 ≤ f → pApp f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx))

/-- the call-like heads of a primary (box G / box B: `args` runs) -/
def HCall (n : Nat) : Prop := ∀ md ks st fin cx, StarN n (.prim md :: ks, st) ([], fin) → CxRel st cx → CxNN st →
  ((∃ x r, st.toks = .id x :: r ∧ findB st.binds x = none) ∨ (∃ t r, st.toks = .k t :: r ∧ 38 < t ∧ t < 48)) →
  PrimConcl n md ks st fin cx

theorem leaf_tc {v : RN} (h : v.kids = []) : v.toNd.tailCont = false := by
  obtain ⟨t, a, b, s, p, ks⟩ := v
  simp only [RN.kids] at h; subst h
  rw [RN.toNd_mk]
  have h0 : (if t = 9 ∧ a < 4 then (match ([] : List RN) with | [] => [] | _ :: r => RN.toNdL r) else RN.toNdL []) = [] := by
    split <;> rfl
  simp only [h0]
  repeat' split
  all_goals first | rfl | simp [Nd.tailCont]

theorem pApp_num {f cx tl v r nx} : pApp (f + 1) cx tl (.num v :: r) nx = pAtom f cx tl (.num v :: r) nx := by
  simp [pApp]
theorem pApp_nil {f cx tl r nx} : pApp (f + 1) cx tl (.k 30 :: .k 31 :: r) nx = pAtom f cx tl (.k 30 :: .k 31 :: r) nx := by
  simp [pApp, primSig]
theorem pApp_paren {f cx tl r nx} : pApp (f + 1) cx tl (.k 6 :: r) nx = pAtom f cx tl (.k 6 :: r) nx := by
  simp [pApp, primSig]
theorem pApp_bound {f cx tl x r nx p} (h : findEnv cx.env x = some p) :
    pApp (f + 1) cx tl (.id x :: r) nx = pAtom f cx tl (.id x :: r) nx := by
  simp [pApp, h]


theorem pApp_bnew {f cx tl r nx} : pApp (f + 2) cx tl (.k 43 :: r) nx = some (.prim 5 [], .s .bf, r, nx) := by
  simp [pApp, primSig, pArgs, dropInp]

theorem findB_mem' {bs : List Bd} {x bd} (h : findB bs x = some bd) : bd ∈ bs := by
  unfold findB at h; exact List.mem_reverse.mp (List.mem_of_find?_eq_some h)

theorem defs_sub_rows {st : St} {d : DefR} (h : d ∈ st.defs) : d ∈ rows st := by simp [rows, h]

/-- a leaf atom on the primary path -/
theorem prim_leaf {n md ks st st1 fin cx} (hc : CxRel st cx) (hnn : CxNN st) (hl : AtomLeaf st st1)
    (hb : ∀ x r, st.toks = .id x :: r → (findB st.binds x).isSome) (h1 : StarN n (ks, st1) ([], fin)) :
    PrimConcl (n + 1) md ks st fin cx := by
  obtain ⟨r, v, hlt, hk, hp, hst⟩ := hl.eff
  refine ⟨v, st1, n, by omega, ?_, by rw [hst]; exact hlt, h1, ?_, fun _ => ?_⟩
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
  · obtain ⟨v', ty, r', hst', hty, hp', hf⟩ := atomLeaf_spec hc hl (md == 1) st.nx
    rw [hst] at hst'
    have hv : v' = v := by
      have := congrArg St.vals hst'; simp at this; exact this.symm
    have hr : r' = r := by
      have := congrArg St.toks hst'; simp at this; exact this.symm
    subst hv hr
    refine ⟨ty, hty, (fun h' => by rw [leaf_tc hk] at h'; cases h'), fun f hf' => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    have hst1 : st1.toks = r' ∧ st1.nx = st.nx := by rw [hst]; exact ⟨rfl, rfl⟩
    rw [hst1.1, hst1.2]
    cases hl with
    | num ht => rw [ht, pApp_num, ← ht]; exact hf g
    | nil ht => rw [ht, pApp_nil, ← ht]; exact hf g
    | bnew ht =>
      rw [ht, pApp_bnew]; have := hf (g + 1); rw [ht] at this; simp [pAtom] at this
      obtain ⟨h1', h2', h3'⟩ := this; rw [← h1', ← h2', ← h3']
    | @loc x r0 bd _ ht hbd _ =>
      have henv := hc.env x; rw [hbd] at henv
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hc.typed x bd hbd)
      have hps : (bdPs bd).isSome := by
        unfold bdPs; split
        · rfl
        · rw [hs]; cases s <;> rfl
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hps
      rw [ht, pApp_bound (p := (bd.slot, p)) (by rw [henv]; simp [hp]), ← ht]; exact hf g
    | cst ht hbd => exact absurd (hb _ _ ht) (by simp [hbd])


theorem pAtom_paren {f cx tl r nx} : pAtom (f + 1) cx tl (.k 6 :: r) nx =
    (pExpr f cx tl r nx).bind fun (e, t, r1, nx1) =>
      match r1 with
      | .k 7 :: r2 => some (e, t, r2, nx1)
      | .k 15 :: _ =>
        (pExpr f cx false r nx).bind fun (e1, t1, r1', nx1') =>
          match tyShape t1 with
          | some s1 => (pTup f cx r1' nx1').map fun (tl', st, r3, nx3) => (.pair [e1, tl'], .s (.p s1 st), r3, nx3)
          | _ => none
      | _ => none := by
  simp only [pAtom]; rfl

/-- a parenthesised expression or a tuple on the primary path -/
theorem prim_paren {n md ks st fin cx r} (hE : ∀ n' ≤ n, ExprSpec n') (hc : CxRel st cx) (hnn : CxNN st)
    (ht : st.toks = .k 6 :: r)
    (h1 : StarN n (.expr 0 (bm (md == 1)) :: .parenClose :: ks, { st with toks := r }) ([], fin)) :
    PrimConcl (n + 1) md ks st fin cx := by
  obtain ⟨e, stE, nE, hnE, hpE, hltE, hEr, _, hnvE, hspE⟩ :=
    hE n (Nat.le_refl _) (bm (md == 1)) _ _ fin cx (by cases md == 1 <;> simp [bm]) h1 (CxRel.transport hc rfl rfl rfl rfl)
      (CxNN.transport hnn rfl rfl rfl)
  match nE, hEr with
  | 0, hEr => exact absurd hEr.zero_nil.1 (by simp)
  | nE + 1, hEr =>
  obtain ⟨k, st1, hs1, h2⟩ := hEr.head
  simp only at hltE
  have l0 : st.toks.length = r.length + 1 := by simp [ht]
  rcases parenClose_inv hs1 with ⟨r2, hr2, rfl, rfl⟩ | ⟨r2, hr2, rfl, rfl⟩
  · -- `( e )`
    simp only [List.nil_append] at h2
    have l1 : r2.length + 1 = stE.toks.length := by simp [hr2]
    refine ⟨e, { stE with toks := r2 }, nE, by omega, ⟨hpE.vals, hpE.binds, hpE.defs, hpE.cur, hpE.arm, hpE.all,
      by have := hpE.toks; simp at this ⊢; omega, hpE.nx⟩, by simp; omega, h2, hnvE, fun hvt => ?_⟩
    obtain ⟨t, ht', hpt, hf⟩ := hspE (by simpa [ParRun.rows] using hvt)
    refine ⟨t, ht', hpt, fun f hf' => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    have pE := hf g (by simp; omega)
    rw [bm_eq] at pE; simp only at pE
    rw [ht, pApp_paren, pAtom_paren, pE]; simp [hr2]
  · -- `( e , … )`
    simp only [List.cons_append, List.nil_append] at h2
    have l1 : r2.length + 1 = stE.toks.length := by simp [hr2]
    obtain ⟨w, st2, n2, hn2, hp2, hlt2, h3, hnv2, hsp2⟩ := tup_sound nE (fun n' hn' => hE n' (by omega)) _ _ fin cx h2
      (CxRel.transport hc (by simp [hpE.binds]) (by simp [hpE.defs]) (by simp [hpE.cur]) (by simp [hpE.arm]))
      (CxNN.transport hnn (by simp [hpE.binds]) (by simp [hpE.defs]) (by simp [hpE.cur]))
    match n2, h3 with
    | 0, h3 => exact absurd h3.zero_nil.1 (by simp)
    | n2 + 1, h3 =>
    obtain ⟨k4, st3, hs4, h4⟩ := h3.head
    obtain ⟨y, x, rest, l, rr, hv4, hxl, hyr, hxp, _, hl, hrr, rfl, hst3⟩ := mkPair_inv hs4
    rw [hp2.vals] at hv4; simp only [List.cons.injEq] at hv4; obtain ⟨rfl, hv4⟩ := hv4
    rw [hpE.vals] at hv4; simp only [List.cons.injEq] at hv4; obtain ⟨rfl, rfl⟩ := hv4
    simp only [List.nil_append] at h4
    have hb2 := hp2.binds; have hd2 := hp2.defs; have hc2 := hp2.cur; have ha2 := hp2.arm; have hl2 := hp2.all
    have ht2 := hp2.toks; have hn2' := hp2.nx
    simp only at hb2 hd2 hc2 ha2 hl2 ht2 hn2' hlt2
    refine ⟨_, st3, n2, by omega, ⟨by rw [hst3], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, h4, ?_, fun hvt => ?_⟩
    · rw [hst3]; simp [hb2, hpE.binds]
    · rw [hst3]; simp [hd2, hpE.defs]
    · rw [hst3]; simp [hc2, hpE.cur]
    · rw [hst3]; simp [ha2, hpE.arm]
    · rw [hst3]; simp [hl2, hpE.all]
    · rw [hst3]; simp; omega
    · rw [hst3]; have := hpE.nx; simp at this ⊢; omega
    · rw [hst3]; simp; omega
    · obtain ⟨s1, hs1, hnn1⟩ := hnvE; obtain ⟨s2, hs2, hnn2⟩ := hnv2
      rw [hxl] at hs1; cases hs1; rw [hyr] at hs2; cases hs2
      exact ⟨.p l rr, by simp [RN.sh], by simp [Sh.nnt, hl, hrr, hnn1, hnn2]⟩
    have hok := hvt.self
    have hni := nodeOK_pair_noInp hok
    have hne := hni e (by simp); have hnw := hni w (by simp)
    obtain ⟨s1, hs1, hnn1⟩ := hnvE
    rw [hxl] at hs1; cases hs1
    obtain ⟨t, ht', hpt, hf⟩ := hspE (by have := hvt.kid (k := e) (by simp); simpa [ParRun.rows] using this)
    obtain ⟨sr, hsr, hf2⟩ := hsp2 (by have := hvt.kid (k := w) (by simp); simpa [ParRun.rows, hpE.defs, hpE.cur] using this)
      (by intro s hs; rw [hyr] at hs; cases hs; exact hrr) hnw
    rw [hyr] at hsr; cases hsr
    have htc : e.toNd.tailCont = false := by
      cases hc' : e.toNd.tailCont
      · rfl
      · have := hpt hc'; rw [hxp] at this; cases this
    refine ⟨.s (.p l rr), ⟨by simp [RN.sh], by simp [RN.isInp, RN.tag], by simp [RN.tag]⟩,
      (fun h' => by rw [pairNode_toNd hne hnw] at h'; simp [Nd.tailCont] at h'), fun f hf' => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    have pE := hf g (by simp; omega)
    rw [bm_eq] at pE; simp only at pE
    have pE' : pExpr g cx false r st.nx = some (e.toNd, t, stE.toks, stE.nx) := by
      cases hmd : (md == 1)
      · rw [hmd] at pE; exact pE
      · rw [hmd] at pE; exact (tl_down g).1 _ _ _ _ pE htc
    have hb : t ≠ .bot := (nobot g).1 _ _ _ _ pE'
    have p2 := hf2 g (by simp; omega)
    simp only at p2
    rw [ht, pApp_paren, pAtom_paren, pE]; simp only [Option.bind_some, hr2]
    rw [pE']; simp only [Option.bind_some, comp_shape ht' hxl hnn1 hl hb hne, hr2]
    rw [p2]
    simp [pairNode_toNd hne hnw, hst3]


theorem prim_sound {n : Nat} (hE : ∀ n' < n, ExprSpec n') (hcall : HCall n) : PrimSpec n := by
  intro md ks st fin cx h hc hnn hmd
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  cases prim_inv hs with
  | ifs hne ht => rcases hmd with h2 | ⟨h32, _⟩
                  · exact absurd h2 hne
                  · exact absurd ht (h32 _)
  | lets hne ht => rcases hmd with h2 | ⟨_, h2'⟩
                   · exact absurd h2 hne
                   · exact absurd ht (h2' _)
  | leaf hl hb => exact prim_leaf hc hnn hl hb (by simpa using h1)
  | paren ht => exact prim_paren (fun n' hn' => hE n' (by omega)) hc hnn ht (by simpa using h1)
  | self ht hb _ _ _ => exact hcall md ks st fin cx h hc hnn (Or.inl ⟨_, _, ht, hb⟩)
  | call ht hb _ _ => exact hcall md ks st fin cx h hc hnn (Or.inl ⟨_, _, ht, hb⟩)
  | primTok ht h1' h2' => exact hcall md ks st fin cx h hc hnn (Or.inr ⟨_, _, ht, h1', h2'⟩)

/-- the expression refinement, given the call-like heads -/
theorem all_specs (hcallOf : ∀ n, (∀ n' < n, ExprSpec n') → HCall n) :
    ∀ n, BinSpec n ∧ LoopSpec n ∧ PrimSpec n ∧ ExprSpec n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  have hB : ∀ n' < n, BinSpec n' := fun n' h => (ih n' h).1
  have hL : ∀ n' < n, LoopSpec n' := fun n' h => (ih n' h).2.1
  have hP : ∀ n' < n, PrimSpec n' := fun n' h => (ih n' h).2.2.1
  have hE : ∀ n' < n, ExprSpec n' := fun n' h => (ih n' h).2.2.2
  exact ⟨bin_of hP hL, loop_sound n hB, prim_sound hE (hcallOf n hE), expr_sound hB hE hP hL⟩

end ParRun
