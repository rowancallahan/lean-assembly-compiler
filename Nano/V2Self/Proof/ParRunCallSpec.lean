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

end ParRun
