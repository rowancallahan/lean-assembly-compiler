/- Nano/V2Self/Proof/ParRunCallSpec: Layer 2 → ParSpec for CALL arguments (box G).
`tyMatch_of`: Par1's argument check (`argOK`: shape code = parameter code, or a numeral / len' for a Nat parameter) together with the
input rule (argument is the input local ⇔ parameter is the input: the deferred validation v210) is ParSpec's `tyMatch`.
`toNdL_dropInp`: the flattener's "skip input locals" is ParSpec's `dropInp`. -/
import Nano.V2Self.Proof.ParRunArgs
namespace ParRun
open ParSpec

theorem tyMatch_of {p : Ps} {v : RN} {ty : Ty} (hv : ValOK v ty) (hn : p ≠ .sh .nt) (hi : p = .inp ↔ v.isInp = true)
    (hok : v.sh = some (psCode p) ∨ (psCode p = .nt ∧ (v.tag = 1 ∨ (v.tag = 9 ∧ v.a = 1)))) : tyMatch p ty = true := by
  obtain ⟨hty, hpe, h9⟩ := hv
  have hsh : v.sh = some (psCode p) ∨ (psCode p = .nt ∧ v.tag = 1) := by
    rcases hok with h | ⟨h1, h2 | ⟨h2, h3⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl (by rw [h1]; exact h9 h2 h3)
  cases ty with
  | bot => simp [TyRel] at hty; rw [hpe] at hty; cases hty
  | inp =>
    obtain ⟨hin, hls⟩ := hty
    have := hi.mpr hin; subst this; rfl
  | lit =>
    obtain ⟨huw, hni⟩ := hty
    cases p with
    | inp => have := hi.mp rfl; rw [hni] at this; cases this
    | fuel => rfl
    | sh s =>
      rcases hsh with h | ⟨h1, _⟩
      · rw [huw] at h; simp [psCode] at h; subst h; rfl
      · exact absurd (by simpa [psCode] using h1) hn
  | s t =>
    obtain ⟨hs, hni, ht1⟩ := hty
    cases p with
    | inp =>
      have := hi.mp rfl; rw [hni] at this; cases this
    | fuel =>
      rcases hsh with h | ⟨_, h2⟩
      · rw [hs] at h; simp [psCode] at h; subst h; rfl
      · exact absurd h2 ht1
    | sh s =>
      rcases hsh with h | ⟨h1, _⟩
      · rw [hs] at h; simp [psCode] at h; subst h; simp [tyMatch]
      · exact absurd (by simpa [psCode] using h1) hn

/-- the input rule, position by position: the parameter is the input iff the argument is the input local -/
inductive InpPair : List Ps → List RN → Prop
  | nil : InpPair [] []
  | cons {p ps v vs} : (p = .inp ↔ v.isInp = true) → InpPair ps vs → InpPair (p :: ps) (v :: vs)

theorem toNdL_cons (n : RN) (r : List RN) : RN.toNdL (n :: r) = if n.isInp then RN.toNdL r else RN.toNd n :: RN.toNdL r := by
  rw [RN.toNdL]

theorem toNdL_dropInp : ∀ {ps : List Ps} {vs : List RN}, InpPair ps vs → RN.toNdL vs = dropInp ps (vs.map RN.toNd) := by
  intro ps vs h
  induction h with
  | nil => simp [RN.toNdL, dropInp]
  | @cons p ps v vs hp _ ih =>
    rw [toNdL_cons, ih]
    by_cases hv : v.isInp = true
    · have := hp.mpr hv; subst this
      simp [hv, dropInp]
    · have hne : p ≠ .inp := fun e => hv (hp.mp e)
      simp only [hv, Bool.false_eq_true, if_false]
      cases p with
      | inp => exact absurd rfl hne
      | fuel => simp [dropInp]
      | sh s => simp [dropInp]

theorem InpPair.len {ps : List Ps} {vs : List RN} (h : InpPair ps vs) : ps.length = vs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem InpPair.get {ps : List Ps} {vs : List RN} (h : InpPair ps vs) :
    ∀ (i : Nat) (h1 : i < ps.length) (h2 : i < vs.length), (ps[i] = .inp ↔ vs[i].isInp = true) := by
  induction h with
  | nil => intro i h1; simp at h1
  | cons hp _ ih =>
    intro i h1 h2
    cases i with
    | zero => exact hp
    | succ i => exact ih i (by simpa using h1) (by simpa using h2)

theorem argsMatch_of : ∀ (ps : List Ps) (vs : List (RN × Ty)), ps.length = vs.length →
    (∀ (i : Nat) (h1 : i < ps.length) (h2 : i < vs.length), tyMatch ps[i] vs[i].2 = true) → ArgsMatch ps vs
  | [], [], _, _ => .nil
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | p :: ps, v :: vs, hl, h =>
    .cons (h 0 (by simp) (by simp)) (argsMatch_of ps vs (by simpa using hl) fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2))

/-- operand `i` (0 = top) of `as.reverse ++ base` is argument `k − 1 − i` -/
theorem operand_idx {α : Type} (l base : List α) (idx : Nat) (h : idx < l.length) :
    (l.reverse ++ base)[l.length - 1 - idx]? = some l[idx] := by
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_reverse (by omega)]
  rw [show l.length - 1 - (l.length - 1 - idx) = idx by omega]
  exact List.getElem?_eq_getElem h

/-- **CALL of a finished def**: the run `args; mkCallN` after the head is `ParSpec.pCallDef`, provided the built node passes the
input rule (deferred validation) -/
theorem defcall_spec {N : Nat} {cx : Cx} (hP : ParenH N cx) {n d j : Nat} {ks : List Frame} {st fin : St} {dR : DefR} {di : DefI}
    {x : List Nat} (hc : CxRel st cx) (hfd : findDef cx.defs x = some (j, di)) (hrow : st.defs[j]? = some dR)
    (hpar : di.params.map psCode = dR.params) (hres : dR.res = some di.res) (hnn : ∀ p ∈ di.params, p ≠ .sh .nt)
    (hd : d = st.vals.length) (hn : n ≤ N)
    (h : StarN n (.args (.df j) di.params.length :: .mkCallN (.df j) d :: ks, st) ([], fin)) :
    ∃ (vs : List (RN × Ty)) (st1 : St) (n' : Nat), n' < n ∧ vs.length = di.params.length ∧
      st1.binds = st.binds ∧ st1.defs = st.defs ∧ st1.cur = st.cur ∧
      StarN n' (ks, { st1 with vals := RN.mk 8 j vs.length dR.res false (vs.map (·.1)) :: st.vals,
                               arena := st1.arena ++ [RN.mk 8 j vs.length dR.res false (vs.map (·.1))] }) ([], fin) ∧
      (InpPair di.params (vs.map (·.1)) →
        ValOK (RN.mk 8 j vs.length dR.res false (vs.map (·.1))) (.s di.res) ∧
        ∃ F, ∀ f, F ≤ f → pCallDef f cx x st.toks st.nx =
          some ((RN.mk 8 j vs.length dR.res false (vs.map (·.1))).toNd, .s di.res, st1.toks, st1.nx)) := by
  obtain ⟨st1, m, n1, hat, rfl, hk⟩ := args_run _ h
  obtain ⟨vs, hlen, hvals, hb, hdd, hcu, hok, F, hp⟩ := args_spec hP hat (by omega) hc
  have hjlt : j < st.defs.length := by
    rcases Nat.lt_or_ge j st.defs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hrow; cases hrow
  have hrows : (rows st1)[j]? = some dR := by
    simp only [rows, hdd]; rw [List.getElem?_append_left hjlt]; exact hrow
  obtain ⟨hall, nd, n', hnode, heq, hrun⟩ := call_tail (c := .df j) (as := (vs.map (·.1)).reverse) (base := st.vals) hvals hd hk
  simp only [List.length_reverse, List.length_map, List.reverse_reverse, callNode, hrows, Option.map_some, Option.some.injEq] at hnode heq hall
  subst hnode
  refine ⟨vs, st1, n', by omega, hlen, hb, hdd, hcu, hrun, fun hinp => ?_⟩
  have hplen : dR.params.length = vs.length := by rw [← hpar]; simp [hlen]
  have har : arity st1 (.df j) = vs.length := by simp [arity, hrows, hplen]
  have hm : ArgsMatch di.params vs := by
    refine argsMatch_of _ _ hlen.symm fun idx h1 h2 => ?_
    obtain ⟨v, w, hv, hw, hcond⟩ := hall (vs.length - 1 - idx) (by omega)
    have e1 := operand_idx (vs.map (·.1)) st.vals idx (by simpa using h2)
    simp only [List.length_map, List.getElem_map] at e1
    rw [hvals, e1] at hv; cases hv
    have e2 : arity st1 (.df j) - (vs.length - 1 - idx + 1) = idx := by rw [har]; omega
    rw [e2] at hw
    have e3 : w = psCode di.params[idx] := by
      simp only [parCode, hrows, Option.bind_some] at hw
      have : dR.params[idx]? = some (psCode di.params[idx]) := by rw [← hpar]; simp [h1]
      rw [this] at hw; cases hw; rfl
    subst e3
    exact tyMatch_of (hok _ (List.getElem_mem h2)) (hnn _ (List.getElem_mem h1))
      (by have := hinp.get idx h1 (by simpa using h2); simpa using this) hcond
  refine ⟨⟨⟨hres, rfl, by simp [RN.tag]⟩, rfl, fun h9 => by cases h9⟩, F + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [pCallDef]
  simp only [hfd]
  rw [hp g (by omega) _ hm]
  simp only [Option.map_some, List.map_map]
  have ht : (RN.mk 8 j vs.length dR.res false (vs.map (·.1))).toNd = .call j (RN.toNdL (vs.map (·.1))) := by
    simp [RN.toNd]
  rw [ht, toNdL_dropInp hinp]
  simp [Function.comp_def]

/-! ## prims -/
theorem primPar_ne_nt (p i : Nat) : primPar p i ≠ .nt := by
  unfold primPar; split <;> (try split) <;> simp

theorem toNd_prim1 (p b : Nat) (sh : Option Sh) (pe : Bool) (kids : List RN) (hp : p < 4) :
    (RN.mk 9 p b sh pe kids).toNd = .prim p (RN.toNdL kids.tail) := by
  rw [RN.toNd.eq_def]
  simp only [hp, and_self, if_true]
  cases kids <;> simp [RN.toNdL]

theorem toNd_prim2 (p b : Nat) (sh : Option Sh) (pe : Bool) (kids : List RN) (hp : ¬ p < 4) :
    (RN.mk 9 p b sh pe kids).toNd = .prim p (RN.toNdL kids) := by
  rw [RN.toNd.eq_def]
  simp only [hp, and_false, if_false]
  simp

theorem prim_toNd {p : Nat} {sh : Option Sh} {ps : List Ps} {kids : List RN} (hi : InpPair ps kids)
    (h4 : p < 4 → ps.head? = some .inp) :
    (RN.mk 9 p 0 sh false kids).toNd = .prim p (dropInp ps (kids.map RN.toNd)) := by
  rw [← toNdL_dropInp hi]
  by_cases hp : p < 4
  · rw [toNd_prim1 _ _ _ _ _ hp]
    cases hi with
    | nil => rfl
    | @cons q qs v vs hq _ =>
      have hq' : q = .inp := by simpa using h4 hp
      have hv : v.isInp = true := hq.mp hq'
      simp [toNdL_cons, hv]
  · rw [toNd_prim2 _ _ _ _ _ hp]

/-- **PRIM application**: the run `args; mkCallN` after a prim token is the prim clause of `ParSpec.pApp`, provided the built node
passes the input rule (deferred validation: rd / len / len' take the input first, no other prim takes it) -/
theorem primcall_spec {N : Nat} {cx : Cx} (hP : ParenH N cx) {n d t : Nat} {ks : List Frame} {st fin : St}
    (hc : CxRel st cx) (h1 : 38 < t) (h2 : t < 48) (hd : d = st.vals.length) (hn : n ≤ N)
    (h : StarN n (.args (.pr (t - 38)) (primAr (t - 38)) :: .mkCallN (.pr (t - 38)) d :: ks, st) ([], fin)) :
    ∃ (ps : List Ps) (vs : List (RN × Ty)) (st1 : St) (n' : Nat), primSig t = some (t - 38, ps, primRes (t - 38)) ∧ n' < n ∧
      vs.length = ps.length ∧ st1.binds = st.binds ∧ st1.defs = st.defs ∧ st1.cur = st.cur ∧
      StarN n' (ks, { st1 with vals := RN.mk 9 (t - 38) 0 (some (primRes (t - 38))) false (vs.map (·.1)) :: st.vals,
                               arena := st1.arena ++ [RN.mk 9 (t - 38) 0 (some (primRes (t - 38))) false (vs.map (·.1))] }) ([], fin) ∧
      (InpPair ps (vs.map (·.1)) →
        ValOK (RN.mk 9 (t - 38) 0 (some (primRes (t - 38))) false (vs.map (·.1))) (.s (primRes (t - 38))) ∧
        ∃ F, ∀ f, F ≤ f → ∀ tl, pApp f cx tl (.k t :: st.toks) st.nx =
          some ((RN.mk 9 (t - 38) 0 (some (primRes (t - 38))) false (vs.map (·.1))).toNd, .s (primRes (t - 38)), st1.toks, st1.nx)) := by
  obtain ⟨ps, hsig, hpl, hcode, hinpi, hnf⟩ := prim_sig h1 h2
  obtain ⟨st1, m, n1, hat, rfl, hk⟩ := args_run _ h
  obtain ⟨vs, hlen, hvals, hb, hdd, hcu, hok, F, hp⟩ := args_spec hP hat (by omega) hc
  obtain ⟨hall, nd, n', hnode, heq, hrun⟩ := call_tail (c := .pr (t - 38)) (as := (vs.map (·.1)).reverse) (base := st.vals) hvals hd hk
  simp only [List.length_reverse, List.length_map, List.reverse_reverse, callNode, Option.some.injEq] at hnode heq hall
  subst hnode
  refine ⟨ps, vs, st1, n', hsig, by omega, by omega, hb, hdd, hcu, hrun, fun hinp => ?_⟩
  have hm : ArgsMatch ps vs := by
    refine argsMatch_of _ _ (by omega) fun idx i1 i2 => ?_
    obtain ⟨v, w, hv, hw, hcond⟩ := hall (vs.length - 1 - idx) (by omega)
    have e1 := operand_idx (vs.map (·.1)) st.vals idx (by simpa using i2)
    simp only [List.length_map, List.getElem_map] at e1
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
    exact tyMatch_of (hok _ (List.getElem_mem i2)) hne
      (by have := hinp.get idx i1 (by simpa using i2); simpa using this) hcond
  have h4 : t - 38 < 4 → ps.head? = some .inp := by
    intro h; have := (hinpi 0).mpr ⟨rfl, h⟩
    cases ps with
    | nil => simp at this
    | cons q qs => simpa using this
  refine ⟨⟨⟨rfl, rfl, by simp [RN.tag]⟩, rfl, fun _ ha => by simp only [RN.a] at ha; rw [ha]; rfl⟩, F + 1, fun f hf tl => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [pApp]
  simp only [hsig]
  rw [hp g (by omega) _ hm]
  simp only [Option.map_some, List.map_map]
  rw [prim_toNd hinp h4]
  simp [Function.comp_def]

/-! ## the input rule from the deferred validation (`nodeOK`, v209) — prims -/
theorem inpPair_of : ∀ (ps : List Ps) (vs : List RN), ps.length = vs.length →
    (∀ (i : Nat) (h1 : i < ps.length) (h2 : i < vs.length), (ps[i] = .inp ↔ vs[i].isInp = true)) → InpPair ps vs
  | [], [], _, _ => .nil
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | p :: ps, v :: vs, hl, h =>
    .cons (h 0 (by simp) (by simp)) (inpPair_of ps vs (by simpa using hl) fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2))

theorem filter_len0 {ks : List RN} (h : (ks.filter RN.isInp).length = 0) : ∀ k ∈ ks, k.isInp = false := by
  intro k hk
  cases hi : k.isInp with
  | false => rfl
  | true =>
    have : k ∈ ks.filter RN.isInp := List.mem_filter.mpr ⟨hk, hi⟩
    rw [List.length_eq_zero_iff.mp h] at this; cases this

/-- a validated PRIM node satisfies the input rule of its signature: rd / len / len' have the input local as first operand and
nowhere else, the other prims have no input operand -/
theorem prim_inpPair {t : Nat} (h1 : 38 < t) (h2 : t < 48) {ps : List Ps} {rs : Sh} (hsig : primSig t = some (t - 38, ps, rs))
    {ds : List DefR} {b : Nat} {sh : Option Sh} {pe : Bool} {kids : List RN} (hl : kids.length = ps.length)
    (hok : nodeOK ds (RN.mk 9 (t - 38) b sh pe kids) = true) : InpPair ps kids := by
  obtain ⟨ps', hsig', _, _, hinpi, _⟩ := prim_sig h1 h2
  rw [hsig] at hsig'; simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hsig'
  obtain ⟨rfl, _⟩ := hsig'
  refine inpPair_of _ _ hl.symm fun i i1 i2 => ?_
  have hget := hinpi i
  rw [List.getElem?_eq_getElem i1] at hget
  simp only [Option.some.injEq] at hget
  rw [hget]
  simp only [nodeOK, RN.kids, RN.tag, RN.a, RN.sh] at hok
  by_cases h4 : t - 38 < 4
  · by_cases hm : (kids.filter RN.isInp).length = 0
    · simp [hm, h4] at hok
    · simp only [hm, if_false, h4, if_true, show ¬ (9 : Nat) = 8 from by decide, show ¬ (9 : Nat) = 6 from by decide,
        Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hm1, hp0⟩ := hok
      cases kids with
      | nil => simp at hm
      | cons k0 r =>
        simp only at hp0
        have hr : (r.filter RN.isInp).length = 0 := by
          simp only [List.filter_cons, hp0, if_true, List.length_cons] at hm1; omega
        cases i with
        | zero => simp [h4, hp0]
        | succ i =>
          have hi : i < r.length := by simpa using i2
          have := filter_len0 hr r[i] (List.getElem_mem hi)
          simp [this]
  · by_cases hm : (kids.filter RN.isInp).length = 0
    · have := filter_len0 hm kids[i] (List.getElem_mem i2)
      simp [this, h4]
    · simp [hm, h4] at hok

end ParRun
