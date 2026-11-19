/- Nano/V2Self/Proof/ParRunSelf: the self-call (CONTINUE) primary, tasks 46 / 54 (box B) ↔ the self clause of ParSpec `pApp`. -/
import Nano.V2Self.Proof.ParRunHCall
namespace ParRun
open ParSpec

theorem selfArgs_inv {st k st'} (h : stepF .selfArgs st = some (k, st')) :
    ∃ fn r1 bd, st.toks = .id fn :: r1 ∧ findB st.binds fn = some bd ∧ bd.sh = some .nt ∧
      k = [.args (.df st.defs.length) (st.cur.params.length - 1), .argCheck (.df st.defs.length) (st.cur.params.length - 1),
           .mkCont st.defs.length (st.cur.params.length - 1)] ∧ st' = { st with toks := r1 } := by
  simp only [stepF] at h
  split at h
  · rename_i fn r1 ht
    split at h
    · rename_i bd hb
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨fn, r1, bd, ht, hb, ‹_›, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

theorem rows_last (st : St) : (rows st)[st.defs.length]? = some st.cur := by simp [rows]
theorem rows_getLast (st : St) : (rows st).getLast? = some st.cur := by simp [rows]

/-- a CONT node is validated: its kid is no input; a PAIR kid with no shape passes the input rule on the tail -/
theorem nodeOK_cont {ds : List DefR} {sh : Option Sh} {c : RN} (h : nodeOK ds (RN.mk 11 0 0 sh true [c]) = true) :
    c.isInp = false := by
  cases hc : c.isInp
  · rfl
  · simp [nodeOK, RN.tag, RN.kids, hc] at h

theorem nodeOK_spair {ds : List DefR} {k : Nat} {kids : List RN} (h : nodeOK ds (RN.mk 6 k 0 none false kids) = true) :
    ∃ d, ds.getLast? = some d ∧ d.params.length = kids.length + 1 ∧ inpMatch d.params.tail false kids = true := by
  simp only [nodeOK, RN.tag, RN.kids, RN.sh, RN.a] at h
  revert h
  cases ds.getLast? with
  | none => simp
  | some d => intro h; simp at h; exact ⟨d, rfl, h.1, h.2⟩

/-- fix M: a CONTINUE over one non-tuple state is checked against the last row like a tuple -/
theorem nodeOK_cont1 {ds : List DefR} {sh : Option Sh} {c : RN} (h : nodeOK ds (RN.mk 11 0 0 sh true [c]) = true)
    (hc : c.sh.isSome = true) :
    ∃ d, ds.getLast? = some d ∧ d.params.length = [c].length + 1 ∧ inpMatch d.params.tail false [c] = true := by
  obtain ⟨t, a, b, s, p, ks⟩ := c
  simp only [RN.sh] at hc
  obtain ⟨s0, rfl⟩ : ∃ s0, s = some s0 := by cases s <;> simp_all
  cases hd : ds.getLast? with
  | none => simp [nodeOK, RN.tag, RN.kids, RN.sh, hd] at h
  | some d =>
    simp [nodeOK, RN.tag, RN.kids, RN.sh, hd] at h
    exact ⟨d, rfl, by simpa using h.2.1, h.2.2⟩

theorem dropInp_ne_nil {ps : List Ps} {as : List Nd} (hl : ps.length = as.length) {i : Nat} (hi : i < ps.length)
    (hp : ps[i] ≠ .inp) : dropInp ps as ≠ [] := by
  induction ps generalizing as i with
  | nil => simp at hi
  | cons p ps ih =>
    cases as with
    | nil => simp at hl
    | cons a as =>
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero] at hp
        cases p <;> simp_all [dropInp]
      | succ i =>
        have := ih (as := as) (by simpa using hl) (by simpa using hi) (by simpa using hp)
        unfold dropInp at this ⊢
        cases p <;> simp_all

/-- the run of `mkCont f j` after the `j` arguments `vs` (source order) were pushed: one CONT node over the kid `c` -/
theorem mkCont_run {f j n : Nat} {ks : List Frame} {st fin : St} {vs base : List RN} {d : DefR}
    (hrow : (rows st)[f]? = some d) (hv : st.vals = vs.reverse ++ base) (hl : vs.length = j) (hj : 1 ≤ j)
    (h : StarN n (.mkCont f j :: ks, st) ([], fin)) :
    ∃ c ar n', n' < n ∧ (j = 1 → vs = [c]) ∧ (j ≠ 1 → c = RN.mk 6 j 0 none false vs) ∧
      StarN n' (ks, { st with vals := RN.mk 11 0 0 d.res true [c] :: base, arena := ar }) ([], fin) := by
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, hrun⟩ := h.head
  simp only [stepF, hrow] at hs
  by_cases h1 : j = 1
  · subst h1
    obtain ⟨v0, rfl⟩ : ∃ v0, vs = [v0] := by
      match vs, hl with
      | [v0], _ => exact ⟨v0, rfl⟩
    simp only [if_true, Option.bind_some] at hs
    obtain ⟨st2, hm, he⟩ := Option.map_eq_some_iff.mp hs
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨_, rfl⟩ := mkNode_inv hm
    refine ⟨v0, st.arena ++ [RN.mk 11 0 0 d.res true [v0]], n, by omega, fun _ => rfl, fun h => absurd rfl h, ?_⟩
    simpa [hv] using hrun
  · simp only [h1, if_false] at hs
    obtain ⟨st2, hm, he⟩ := Option.map_eq_some_iff.mp hs
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨st3, hm1, hm2⟩ := Option.bind_eq_some_iff.mp hm
    obtain ⟨_, rfl⟩ := mkNode_inv hm1
    obtain ⟨_, rfl⟩ := mkNode_inv hm2
    have e1 : List.take j (vs.reverse ++ base) = vs.reverse := by
      rw [List.take_append_of_le_length (by simp [hl])]; rw [← hl, ← List.length_reverse]; exact List.take_length
    have e2 : List.drop j (vs.reverse ++ base) = base := by
      rw [List.drop_append_of_le_length (by simp [hl])]; simp [← hl]
    refine ⟨RN.mk 6 j 0 none false vs, st.arena ++ [RN.mk 6 j 0 none false vs] ++ [RN.mk 11 0 0 d.res true [RN.mk 6 j 0 none false vs]], n, by omega, fun h => absurd h h1, fun _ => rfl, ?_⟩
    simpa [hv, e1, e2] using hrun

theorem pApp_self {g : Nat} {cx : Cx} {x fn : List Nat} {r1 : List Tok} {nx sl : Nat} {sps : List Ps}
    (henv : findEnv cx.env x = none) (hs : cx.self = some (x, sps)) (hf : findEnv cx.env fn = some (sl, .fuel)) :
    pApp (g + 1) cx true (.id x :: .id fn :: r1) nx = (pArgs g cx sps r1 nx).bind fun (as, r2, nx2) =>
      match dropInp sps (as.map (·.1)) with
      | [] => none
      | cs => some (.cont (mkPairFlat cs), .bot, r2, nx2) := by
  simp only [pApp, henv, hs, hf, beq_self_eq_true, if_true]; rfl

theorem toNd_spair {k : Nat} {kids : List RN} : (RN.mk 6 k 0 none false kids).toNd = mkPairFlat (RN.toNdL kids) := by
  rw [RN.toNd_mk]; simp only
  rw [if_neg (by omega)]
  simp only [show ¬((6 : Nat) = 1) by omega, show ¬((6 : Nat) = 2) by omega, show ¬((6 : Nat) = 3) by omega,
    show ¬((6 : Nat) = 4) by omega, show ¬((6 : Nat) = 5) by omega, if_true, if_false]
  cases RN.toNdL kids with
  | nil => rfl
  | cons a l => cases l <;> rfl

theorem toNd_cont {sh : Option Sh} {c : RN} (hc : c.isInp = false) : (RN.mk 11 0 0 sh true [c]).toNd = .cont c.toNd := by
  rw [RN.toNd_mk]; simp [RN.toNdL, hc]

theorem firstLs_01 {ws : List Sh} (h0 : FirstLs ws 0) (h1 : FirstLs ws 1) : False := h1.2 0 (by omega) h0.1

/-- **self-call** (`PrimCase.self`: tasks 3 → 46 → 44/47/54) -/
theorem hcall_self {n : Nat} (hE : ∀ n' < n, ExprSpec n') {ks : List Frame} {st fin : St} {cx : Cx} {x : List Nat}
    {r : List Tok} (h : StarN n (.prim 1 :: ks, st) ([], fin)) (hc : CxRel st cx) (hnn : CxNN st)
    (ht : st.toks = .id x :: r) (hb : findB st.binds x = none) (hj : findD (rows st) x = some st.defs.length)
    (harm : st.arm = true) :
    PrimConcl n 1 ks st fin cx := by
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n0 + 1, h =>
  obtain ⟨k, st0, hs, hrun⟩ := h.head
  have hstep : stepF (.prim 1) st = some ([.selfArgs], { st with toks := r }) := by
    have hj' : findD (rows { st with toks := r }) x = some st.defs.length := hj
    simp [stepF, ht, hb, hj']; simp [harm]
  rw [hstep] at hs; cases hs
  match n0, hrun with
  | 0, hrun => exact absurd hrun.zero_nil.1 (by simp)
  | n1 + 1, hrun =>
  obtain ⟨k2, st2, hs2, hrun2⟩ := hrun.head
  obtain ⟨fn, r1, bd, hr, hbd, hnt, rfl, rfl⟩ := selfArgs_inv hs2
  simp only at hr hbd hrun2
  subst hr
  have hcn : st.cur.name = x := by
    rw [findD_rows] at hj; split at hj
    · assumption
    · exact absurd (findD_ltG hj) (by omega)
  obtain ⟨sps, hself, hsne, hpar, hinv, hnnp⟩ := hc.self harm
  rw [hcn] at hself
  have hspl : sps.length = st.cur.params.length - 1 := by
    have := congrArg List.length hpar; simpa using this
  have hj1 : 1 ≤ st.cur.params.length - 1 := by
    have : sps.length ≠ 0 := fun h0 => hsne (List.eq_nil_of_length_eq_zero h0)
    omega
  obtain ⟨st3, m, n2, hat, hn1, hk⟩ := args_run _ hrun2
  obtain ⟨vs, hlen, hvals, hbb, hd, hcu, harm3, hall', hout', htk, hnx, hshs, hsps⟩ :=
    argsV (N := m + 1) (fun k hk => hE k (by omega)) hat (by omega)
      (CxRel.transport hc rfl rfl rfl rfl) (CxNN.transport hnn rfl rfl rfl)
  obtain ⟨hok, n3, hn2, hk3⟩ := argCheck_run _ hk
  have hrows3 : (rows st3)[st.defs.length]? = some st.cur := by rw [rows_eq hd hcu]; exact rows_last st
  obtain ⟨c, ar, n4, hn4, hc1, hc2, hfin⟩ := mkCont_run hrows3 hvals hlen hj1 hk3
  have hmemR : st.cur ∈ rows st := List.mem_of_getElem? (rows_last st)
  refine ⟨RN.mk 11 0 0 st.cur.res true [c], { st3 with vals := RN.mk 11 0 0 st.cur.res true [c] :: st.vals, arena := ar },
    n4, by omega, ⟨rfl, hbb, hd, hcu, by simpa using harm3, by simpa using hall', by rw [ht]; simp at htk ⊢; omega,
      by simpa using hnx, by simpa using hout'⟩, by rw [ht]; simp at htk ⊢; omega, hfin, (hnn.2 _ hmemR).1, fun hvt => ?_⟩
  have hci : c.isInp = false := nodeOK_cont hvt.self
  have hvc : VT (rows st) c := hvt.kid (by simp)
  have hvts : ∀ v ∈ vs, VT (rows st) v := by
    by_cases h1 : st.cur.params.length - 1 = 1
    · rw [hc1 h1]; intro v hv; simp at hv; subst hv; exact hvc
    · rw [hc2 h1] at hvc; intro v hv; exact hvc.kid hv
  have hlsp : vs.length = sps.length := by omega
  obtain ⟨vts, hmap, hfacts, hpargs⟩ := hsps hvts
  have hinp : InpPair sps vs := by
    by_cases h1 : st.cur.params.length - 1 = 1
    · have e := hc1 h1
      -- the lone state value has a shape (it is an argument value), so the CONT node's own check applies (fix M)
      have hcs : c.sh.isSome = true := by
        obtain ⟨⟨c', ty⟩, hcm, rfl⟩ : ∃ q ∈ vts, q.1 = c := by
          have : c ∈ vts.map (·.1) := by rw [hmap, e]; simp
          simpa using this
        obtain ⟨f1, f2, _⟩ := hfacts _ hcm
        cases ty with
        | s s => simp [f1.1]
        | lit => simp [f1.1]
        | inp => simp [f1.2]
        | bot => exact absurd rfl f2
      obtain ⟨d, hd1, _, hm⟩ := nodeOK_cont1 hvt.self hcs
      rw [rows_getLast] at hd1; cases hd1
      rw [e]; rw [e] at hlsp
      exact def_inpPair hinv hlsp hm
    · rw [hc2 h1] at hvc
      obtain ⟨d, hd1, _, hm⟩ := nodeOK_spair hvc.self
      rw [rows_getLast] at hd1; cases hd1
      exact def_inpPair hinv hlsp hm
  have hlv : vts.length = vs.length := by rw [← hmap]; simp
  have hrw3 : rows st3 = rows st := rows_eq hd hcu
  have hm : ArgsMatch sps vts := by
    refine argsMatch_of _ _ (by omega) fun idx i1 i2 => ?_
    have i3 : idx < vs.length := by omega
    obtain ⟨v, w, hv, hw, hcond⟩ := hok (vs.length - 1 - idx) (by omega)
    have e1 := operand_idx vs st.vals idx i3
    rw [hvals, e1] at hv; cases hv
    have har1 : arity st3 (.df st.defs.length) = st.cur.params.length := by simp [arity, hrw3, rows_last]
    have e2 : arity st3 (.df st.defs.length) - (vs.length - 1 - idx + 1) = idx + 1 := by rw [har1]; omega
    rw [e2] at hw
    have e3 : w = psCode sps[idx] := by
      simp only [parCode, hrw3, rows_last, Option.bind_some] at hw
      have : st.cur.params.tail[idx]? = some (psCode sps[idx]) := by rw [← hpar]; simp [i1]
      rw [List.getElem?_tail] at this
      rw [this] at hw; cases hw; rfl
    subst e3
    have hvi : (vts[idx]).1 = vs[idx] := by
      have := congrArg (fun l => l[idx]?) hmap
      simpa [List.getElem?_eq_getElem i2, List.getElem?_eq_getElem i3] using this
    obtain ⟨f1, f2, f3⟩ := hfacts _ (List.getElem_mem i2)
    rw [hvi] at f1 f3
    exact tyMatch_of2 f1 f2 f3 (hnnp _ (List.getElem_mem i1)) (by have := hinp.get idx i1 i3; simpa using this) hcond
  -- the spec side
  have henv : findEnv cx.env x = none := by rw [hc.env x, hb]; rfl
  have hbi : bd.inp = false := by
    cases hi : bd.inp
    · rfl
    · have := hc.inp fn bd hbd hi; rw [hnt] at this; cases this
  have hfuel : findEnv cx.env fn = some (bd.slot, .fuel) := by
    rw [hc.env fn, hbd]; simp [bdPs, hbi, hnt]
  have hne : RN.toNdL vs ≠ [] := by
    rw [toNdL_dropInp hinp]
    by_cases h1 : st.cur.params.length - 1 = 1
    · refine dropInp_ne_nil (by simp; omega) (i := 0) (by omega) fun e => ?_
      have e' := hc1 h1; subst e'
      have := (hinp.get 0 (by omega) (by simp)).mp e
      simp [hci] at this
    · by_cases e0 : sps[0]'(by omega) = .inp
      · refine dropInp_ne_nil (by simp; omega) (i := 1) (by omega) fun e1 => ?_
        exact firstLs_01 ((hinv 0 (by omega)).mp e0) ((hinv 1 (by omega)).mp e1)
      · exact dropInp_ne_nil (by simp; omega) (i := 0) (by omega) e0
  have htn : (RN.mk 11 0 0 st.cur.res true [c]).toNd = .cont (mkPairFlat (RN.toNdL vs)) := by
    rw [toNd_cont hci]
    by_cases h1 : st.cur.params.length - 1 = 1
    · have e := hc1 h1; subst e; simp [RN.toNdL, hci, mkPairFlat]
    · rw [hc2 h1, toNd_spair]
  refine ⟨.bot, rfl, fun _ => rfl, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [ht, show ((1 : Nat) == 1) = true from rfl, pApp_self henv hself hfuel, hpargs sps hm g (by rw [ht] at hf; simp at hf ⊢; omega)]
  simp only [Option.bind_some, List.map_map]
  have hd2 : dropInp sps (List.map ((fun x => x.fst) ∘ fun p => (p.1.toNd, p.2)) vts) = RN.toNdL vs := by
    rw [toNdL_dropInp hinp, ← hmap]; simp [Function.comp_def]
  rw [hd2, htn]
  revert hne
  cases RN.toNdL vs with
  | nil => intro h; exact absurd rfl h
  | cons a l => intro _; rfl

/-- `HCall` (B's hypothesis in `all_specs`): def call (G), prim application (G), self-call (B) -/
theorem hcall_all (n : Nat) (hE : ∀ n' < n, ExprSpec n') : HCall n := by
  intro md ks st fin cx h hc hnn hh
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n0 + 1, h =>
  obtain ⟨k, st0, hs, hrun⟩ := h.head
  cases prim_inv hs with
  | ifs _ ht => rcases hh with ⟨x, r, ht', _⟩ | ⟨t, r, ht', h1, h2⟩ <;> rw [ht] at ht' <;> simp at ht' <;> omega
  | lets _ ht => rcases hh with ⟨x, r, ht', _⟩ | ⟨t, r, ht', h1, h2⟩ <;> rw [ht] at ht' <;> simp at ht' <;> omega
  | leaf _ hbd =>
    rcases hh with ⟨x, r, ht, hb⟩ | ⟨t, r, ht, h1, h2⟩
    · have := hbd x r ht; rw [hb] at this; cases this
    · exact prim_leaf hc hnn ‹_› hbd (by simpa using hrun)
  | paren ht => rcases hh with ⟨x, r, ht', _⟩ | ⟨t, r, ht', h1, h2⟩ <;> rw [ht] at ht' <;> simp at ht' <;> omega
  | self ht hb hj hmd harm => subst hmd; exact hcall_self hE h hc hnn ht hb hj harm
  | call ht hb hj hne => exact hcall_def hE h hc hnn ht hb hj hne
  | primTok ht h1 h2 => exact hcall_prim hE h hc hnn ht h1 h2

/-- **the expression refinement** (Layer 2 → ParSpec), for every run length -/
theorem expr_specs : ∀ n, BinSpec n ∧ LoopSpec n ∧ PrimSpec n ∧ ExprSpec n := all_specs hcall_all

end ParRun
