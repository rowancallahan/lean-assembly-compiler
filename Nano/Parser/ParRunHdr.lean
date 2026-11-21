/- Nano/Parser/ParRunHdr: Layer-2 def headers ↔ ParSpec (parser lead), pure.
* `group_spec`: the `group` frame collects the identifiers of a binder group exactly as `pBinders.ids`, as untyped placeholders. -/
import Nano.Parser.ParRunDefs
import Nano.Parser.ParRunRow
namespace ParRun
open ParSpec

/-- an untyped binder placeholder -/
def phB (x : List Nat) : Bd := ⟨x, 0, none, false⟩

theorem ids_id (x : List Nat) (r : List Tok) :
    pBinders.ids (.id x :: r) = (pBinders.ids r).map fun (l, r') => (x :: l, r') := by
  rw [pBinders.ids]

theorem ids_k (t : Nat) (r : List Tok) : pBinders.ids (.k t :: r) = some ([], .k t :: r) := by
  rw [pBinders.ids.eq_def]

theorem ids_len : ∀ (ts : List Tok) (ns : List (List Nat)) (r : List Tok), pBinders.ids ts = some (ns, r) → r.length ≤ ts.length
  | [], ns, r, h => by rw [pBinders.ids.eq_def] at h; simp at h; simp [← h.2]
  | .id x :: t, ns, r, h => by
    rw [ids_id] at h
    obtain ⟨⟨l, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2; obtain ⟨_, rfl⟩ := h2
    have := ids_len t l r' h1; simp; omega
  | .k t :: tl, ns, r, h => by rw [ids_k] at h; simp at h; simp [← h.2]
  | .num v :: tl, ns, r, h => by rw [pBinders.ids.eq_def] at h; simp at h; simp [← h.2]

theorem group_spec : ∀ (n : Nat) {a : Nat} {ks : List Frame} {st fin : St}, StarN n (.group a :: ks, st) ([], fin) →
    ∃ ns r n', n' < n ∧ pBinders.ids st.toks = some (ns, .k 8 :: r) ∧ a < st.binds.length + ns.length ∧
      Star (.group a :: ks, st) (.tyAtom :: .rparen :: .assign a (st.binds.length + ns.length - a) :: .binders :: ks,
        { st with toks := r, binds := st.binds ++ ns.map phB }) ∧
      StarN n' (.tyAtom :: .rparen :: .assign a (st.binds.length + ns.length - a) :: .binders :: ks,
        { st with toks := r, binds := st.binds ++ ns.map phB }) ([], fin) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro a ks st fin h
  match n, h with
  | n + 1, h =>
    obtain ⟨k, st1, h1, h2⟩ := h.head
    have hs1 := Star.one (fs := ks) h1
    simp only [stepF] at h1
    split at h1
    · rename_i x r ht
      cases h1
      obtain ⟨ns, r', n', hn, hi, ha, hst, h3⟩ := ih n (by omega) h2
      refine ⟨x :: ns, r', n', by omega, ?_, ?_, ?_, ?_⟩
      · rw [ht, ids_id]; simp only at hi; rw [hi]; rfl
      · simp at ha ⊢; omega
      · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.append_assoc,
          List.cons_append, List.nil_append] at hst hs1 ⊢
        have e1 : st.binds.length + 1 + ns.length = st.binds.length + (ns.length + 1) := by omega
        rw [e1] at hst
        exact hs1.trans hst
      · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.append_assoc,
          List.cons_append, List.nil_append] at h3 ⊢
        have e1 : st.binds.length + 1 + ns.length = st.binds.length + (ns.length + 1) := by omega
        rw [e1] at h3
        exact h3
    · rename_i r ht
      split at h1
      · cases h1
        rename_i hlt
        exact ⟨[], r, n, by omega, by rw [ht, ids_k], by simpa using hlt, by simpa using hs1, by simpa using h2⟩
      · cases h1
    · cases h1


theorem go_nil (p : Ps) (s : Nat) : bindSlots.go p s [] = ([], [], s) := by rw [bindSlots.go]
theorem go_cons (p : Ps) (s : Nat) (x : List Nat) (l : List (List Nat)) :
    bindSlots.go p s (x :: l) = ((x, s, p) :: (bindSlots.go p (s + p.width) l).1, p :: (bindSlots.go p (s + p.width) l).2.1,
      (bindSlots.go p (s + p.width) l).2.2) := by
  rw [bindSlots.go]

/-- a spec binding as a Layer-2 binding -/
def toBd : List Nat × Nat × Ps → Bd := fun (x, s, p) => ⟨x, s, some (psCode p), p == .inp⟩

/-- `pickPs` vs the Layer-2 input flag -/
theorem pick_ok {t : TyR} (ht : t ≠ .sh .ls) (used single : Bool) :
    psCode (pickPs used single t).1 = trRes t ∧
      ((pickPs used single t).1 == .inp) = (trRes t == .ls && single && !used) ∧ (pickPs used single t).1 ≠ .fuel := by
  cases t with
  | lst => cases used <;> cases single <;> simp [pickPs, psCode, trRes]
  | sh s =>
    have h1 : (s == Sh.ls) = false := by simpa using (fun e => ht (by rw [e]) : s ≠ .ls)
    refine ⟨rfl, ?_, by simp [pickPs]⟩
    simp [pickPs, trRes, h1]

theorem Ps.width_code {p : Ps} (h : p ≠ .fuel) : (if (p == .inp) = true then 0 else (psCode p).width) = p.width := by
  cases p with
  | inp => rfl
  | fuel => exact absurd rfl h
  | sh s => simp [psCode, Ps.width]

/-- **assign loop**: the placeholders `ns` of a binder group of type `t` are typed in order, exactly as `bindSlots.go`
(slots from `nx`, the kind `p` from `pickPs`), the row gets one parameter code per name -/
theorem assign_spec {t : TyR} (ht : t ≠ .sh .ls) {used : Bool} {sz : Nat} :
    ∀ (ns : List (List Nat)) (n a : Nat) {ks : List Frame} {st fin : St} (P : List Bd),
    StarN n (.assign a sz :: ks, st) ([], fin) → st.ty = some (trRes t) → st.binds = P ++ ns.map phB → a = P.length →
    (sz = 1 → ns ≠ [] → P.any Bd.inp = used) → (sz = 1 → ns.length ≤ 1) →
    ∃ n', n' < n ∧ (ns ≠ [] → trRes t ≠ .nt) ∧ (ns ≠ [] → t = .lst → sz ≠ 1 → P.any Bd.inp = true) ∧
      Star (.assign a sz :: ks, st) (ks, { st with
        binds := P ++ List.map toBd (bindSlots.go (pickPs used (sz == 1) t).1 st.nx ns).1
        nx := (bindSlots.go (pickPs used (sz == 1) t).1 st.nx ns).2.2
        cur := { st.cur with
          params := st.cur.params ++ List.map psCode (bindSlots.go (pickPs used (sz == 1) t).1 st.nx ns).2.1
          nni := st.cur.nni + (if (pickPs used (sz == 1) t).1 = .inp then 0 else ns.length) } }) ∧
      StarN n' (ks, { st with
        binds := P ++ List.map toBd (bindSlots.go (pickPs used (sz == 1) t).1 st.nx ns).1
        nx := (bindSlots.go (pickPs used (sz == 1) t).1 st.nx ns).2.2
        cur := { st.cur with
          params := st.cur.params ++ List.map psCode (bindSlots.go (pickPs used (sz == 1) t).1 st.nx ns).2.1
          nni := st.cur.nni + (if (pickPs used (sz == 1) t).1 = .inp then 0 else ns.length) } }) ([], fin) := by
  intro ns
  induction ns with
  | nil =>
    intro n a ks st fin P h hty hb ha _ _
    match n, h with
    | n + 1, h =>
      obtain ⟨k, st1, h1, h2⟩ := h.head
      have hs1 := Star.one (fs := ks) h1
      have hl : a = st.binds.length := by rw [hb, ha]; simp
      simp only [stepF, hl, if_true] at h1
      cases h1
      have e : ({ st with
          binds := P ++ List.map toBd (bindSlots.go (pickPs used (sz == 1) t).1 st.nx []).1
          nx := (bindSlots.go (pickPs used (sz == 1) t).1 st.nx []).2.2
          cur := { st.cur with
            params := st.cur.params ++ List.map psCode (bindSlots.go (pickPs used (sz == 1) t).1 st.nx []).2.1
            nni := st.cur.nni + (if (pickPs used (sz == 1) t).1 = .inp then 0 else ([] : List (List Nat)).length) } } : St) = st := by
        simp only [go_nil, List.map_nil, List.append_nil, List.length_nil, ite_self, Nat.add_zero]
        simp only [List.map_nil, List.append_nil] at hb
        rw [← hb]
      exact ⟨n, by omega, fun e => absurd rfl e, fun e => absurd rfl e, by rw [e]; simpa using hs1, by rw [e]; simpa using h2⟩
  | cons x ns ih =>
    intro n a ks st fin P h hty hb ha hu hsz
    match n, h with
    | n + 1, h =>
      obtain ⟨k, st1, h1, h2⟩ := h.head
      have hs1 := Star.one (fs := ks) h1
      have hne : a ≠ st.binds.length := by rw [hb, ha]; simp
      have hget : st.binds[a]? = some (phB x) := by rw [hb, ha]; simp
      have htake : st.binds.take a = P := by rw [hb, ha]; simp
      simp only [stepF, hne, if_false, hty, hget, htake] at h1
      split at h1
      · cases h1
      rename_i hnt
      split at h1
      · cases h1
      rename_i hJ
      by_cases hcap : 2 ^ 20 ≤ (if (trRes t == Sh.ls && sz == 1 && !P.any Bd.inp) = true then st.nx else st.nx + (trRes t).width)
      · simp only [hcap, ↓reduceIte] at h1; cases h1
      simp only [hcap, ↓reduceIte] at h1
      cases h1
      obtain ⟨pk, pw, pf⟩ := pick_ok ht used (sz == 1)
      have hn1 : (trRes t == .ls && sz == 1 && !P.any Bd.inp) = ((pickPs used (sz == 1) t).1 == .inp) := by
        rw [pw]
        by_cases h1 : sz = 1
        · rw [hu h1 (by simp)]
        · have e : (sz == 1) = false := by simpa using h1
          rw [e]; simp
      have hset : st.binds.set a ⟨(phB x).name, st.nx, some (trRes t), trRes t == .ls && sz == 1 && !P.any Bd.inp⟩ =
          (P ++ [toBd (x, st.nx, (pickPs used (sz == 1) t).1)]) ++ ns.map phB := by
        rw [hb, ha, hn1]; simp [toBd, phB, pk]
      rw [hset, List.singleton_append] at h2
      rw [hset, List.singleton_append] at hs1
      obtain ⟨n', hn', _, _, hst, h3⟩ := ih n (a + 1) (P ++ [toBd (x, st.nx, (pickPs used (sz == 1) t).1)]) h2
        rfl rfl (by simp [ha])
        (fun e1 e2 => absurd (List.eq_nil_of_length_eq_zero (by have := hsz e1; rw [List.length_cons] at this; omega)) e2)
        (fun e1 => by have := hsz e1; rw [List.length_cons] at this; omega)
      have both := And.intro (hs1.trans hst) h3
      refine ⟨n', by omega, fun _ => hnt, fun _ hl hs1' => ?_, ?_⟩
      · subst hl
        cases hc : P.any Bd.inp
        · exact absurd ⟨rfl, hs1', by simp [hc]⟩ hJ
        · rfl
      rw [go_cons]
      rw [hn1] at both
      generalize (pickPs used (sz == 1) t).1 = p at pk pf both ⊢
      rw [← pk] at both hty
      cases p with
      | inp => simpa [Ps.width, toBd, List.append_assoc, hty] using both
      | fuel => exact absurd rfl pf
      | sh s => simpa [Ps.width, psCode, toBd, List.append_assoc, Nat.add_assoc, Nat.add_comm 1, hty] using both


theorem any_go (p : Ps) : ∀ (s : Nat) (ns : List (List Nat)), ns ≠ [] →
    (List.map toBd (bindSlots.go p s ns).1).any Bd.inp = (p == .inp) := by
  intro s ns hne
  induction ns generalizing s with
  | nil => exact absurd rfl hne
  | cons x l ih =>
    rw [go_cons]
    cases l with
    | nil => simp [go_nil, toBd]
    | cons y l' =>
      simp only [List.map_cons, List.any_cons]
      rw [ih _ (by simp)]
      simp [toBd]

theorem mem_go (p : Ps) : ∀ (s : Nat) (ns : List (List Nat)) (q : Ps), q ∈ (bindSlots.go p s ns).2.1 → q = p := by
  intro s ns q hq
  induction ns generalizing s with
  | nil => simp [go_nil] at hq
  | cons x l ih =>
    rw [go_cons] at hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · rfl
    · exact ih _ hq

theorem pick_used (used single : Bool) (t : TyR) :
    (pickPs used single t).2 = (used || ((pickPs used single t).1 == .inp)) := by
  cases t with
  | sh s => simp [pickPs]
  | lst => cases used <;> cases single <;> simp [pickPs]

theorem bindSlots_nil (s : Nat) (used : Bool) : bindSlots s used [] = ([], [], s) := by rw [bindSlots]

theorem bindSlots_cons (s : Nat) (used : Bool) (ns : List (List Nat)) (t : TyR) (g : List (List (List Nat) × TyR)) :
    bindSlots s used ((ns, t) :: g) =
      ((bindSlots.go (pickPs used (ns.length == 1) t).1 s ns).1 ++
          (bindSlots (bindSlots.go (pickPs used (ns.length == 1) t).1 s ns).2.2 (pickPs used (ns.length == 1) t).2 g).1,
        (bindSlots.go (pickPs used (ns.length == 1) t).1 s ns).2.1 ++
          (bindSlots (bindSlots.go (pickPs used (ns.length == 1) t).1 s ns).2.2 (pickPs used (ns.length == 1) t).2 g).2.1,
        (bindSlots (bindSlots.go (pickPs used (ns.length == 1) t).1 s ns).2.2 (pickPs used (ns.length == 1) t).2 g).2.2) := by
  rw [bindSlots.eq_2]


/-- Layer 2's fix J on the parsed groups: a multi-name `List UInt8` group only after the input -/
def FixJ : Bool → List (List (List Nat) × TyR) → Prop
  | _, [] => True
  | used, (ns, t) :: g => (t = .lst → ns.length ≠ 1 → used = true) ∧ FixJ (pickPs used (ns.length == 1) t).2 g

/-- **binder list** `(a b : T) (c : U) … :` ↔ `pBinders` + `bindSlots` from the current slot / input flag -/
theorem binders_spec : ∀ (n : Nat) {ks : List Frame} {st fin : St} (b : Bool), StarN n (.binders :: ks, st) ([], fin) →
    ∃ groups r n' ty' nni', n' < n ∧ r.length < st.toks.length ∧
      (∀ f, 3 * st.toks.length + 3 ≤ f → pBinders f b st.toks = some (groups, .k 8 :: r)) ∧
      (∀ p ∈ (bindSlots st.nx (st.binds.any Bd.inp) groups).2.1, p ≠ .fuel ∧ psCode p ≠ .nt ∧ (psCode p).nnt = true) ∧
      FixJ (st.binds.any Bd.inp) groups ∧
      Star (.binders :: ks, st) (.tyAtom :: .plainBody :: ks, { st with
        toks := r
        binds := st.binds ++ List.map toBd (bindSlots st.nx (st.binds.any Bd.inp) groups).1
        nx := (bindSlots st.nx (st.binds.any Bd.inp) groups).2.2
        ty := ty'
        cur := { st.cur with
          params := st.cur.params ++ List.map psCode (bindSlots st.nx (st.binds.any Bd.inp) groups).2.1
          nni := nni' } }) ∧
      StarN n' (.tyAtom :: .plainBody :: ks, { st with
        toks := r
        binds := st.binds ++ List.map toBd (bindSlots st.nx (st.binds.any Bd.inp) groups).1
        nx := (bindSlots st.nx (st.binds.any Bd.inp) groups).2.2
        ty := ty'
        cur := { st.cur with
          params := st.cur.params ++ List.map psCode (bindSlots st.nx (st.binds.any Bd.inp) groups).2.1
          nni := nni' } }) ([], fin) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro ks st fin b h
  match n, h with
  | n + 1, h =>
    obtain ⟨k, st1, h1, hs1, h2⟩ := h.head_star
    simp only [stepF] at h1
    split at h1
    · -- `(` : a group
      rename_i r0 ht0
      cases h1
      simp only [List.singleton_append] at h2 hs1
      obtain ⟨ns, r1, n2, hn2, hids, hlt, hsg, h3⟩ := group_spec n h2
      have hne : ns ≠ [] := by intro e; subst e; simp at hlt
      obtain ⟨t, r2, n3, hn3, hl2, hpTy, hst4, h4, hnnt⟩ := ty_star h3
      dsimp only at hl2 hpTy
      have htl : t ≠ .sh .ls := (pTy_noLs (2 * r1.length + 2)).2 r1 t r2 (hpTy _ (Nat.le_refl _))
      match n3, h4 with
      | n3 + 1, h4 =>
      obtain ⟨k5, st5, h5, hs5, h6⟩ := h4.head_star
      simp only [stepF, St.withTy] at h5
      obtain ⟨r4, rfl⟩ : ∃ r4, r2 = .k 7 :: r4 := by
        match r2, h5 with
        | .k 7 :: r4, _ => exact ⟨r4, rfl⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl⟩ := h5
      have hsz : st.binds.length + ns.length - st.binds.length = ns.length := by omega
      simp only [List.nil_append, hsz] at h6 hs5 hst4 hsg
      obtain ⟨n4, hn4, hnt, hfj, hsa, h7⟩ := assign_spec htl (used := st.binds.any Bd.inp) ns n3 st.binds.length st.binds h6 rfl rfl rfl
        (fun _ _ => rfl) (fun e => by omega)
      obtain ⟨g, r, n5, ty', nni', hn5, hlr, hpB, hps, hfj', hst8, h8⟩ := ih n4 (by omega) false h7
      have both := And.intro (hs1.trans (hsg.trans (hst4.trans (hs5.trans (hsa.trans hst8))))) h8
      dsimp only at hlr hpB hps hfj' both
      have hused : (st.binds ++ List.map toBd (bindSlots.go (pickPs (st.binds.any Bd.inp) (ns.length == 1) t).1 st.nx ns).1).any
          Bd.inp = (pickPs (st.binds.any Bd.inp) (ns.length == 1) t).2 := by
        rw [List.any_append, any_go _ _ _ hne, pick_used]
      rw [hused] at hps hfj' both
      refine ⟨(ns, t) :: g, r, n5, ty', nni', by omega, ?_, ?_, ?_, ⟨fun e1 e2 => hfj hne e1 (by omega), hfj'⟩, ?_⟩
      · have l1 := ids_len _ _ _ hids
        simp only [List.length_cons] at l1 hl2
        rw [ht0]; simp; omega
      · intro f hf
        have l1 := ids_len _ _ _ hids
        simp only [List.length_cons] at l1
        rw [ht0] at hf ⊢
        simp only [List.length_cons] at hf
        obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [pBinders.eq_def]
        simp only []
        rw [hids]
        obtain ⟨y, ys, rfl⟩ : ∃ y ys, ns = y :: ys := by cases ns <;> simp_all
        have l2 : r4.length + 1 = (Tok.k 7 :: r4).length := by simp
        simp only [Option.bind_some]
        rw [hpTy f (by omega)]
        simp only [Option.bind_some]
        cases t <;> simp [hpB f (by omega)]
      · intro p hp
        rw [bindSlots_cons] at hp
        rcases List.mem_append.mp hp with hp | hp
        · have := mem_go _ _ _ _ hp
          subst this
          obtain ⟨pk, _, pf⟩ := pick_ok htl (st.binds.any Bd.inp) (ns.length == 1)
          exact ⟨pf, by rw [pk]; exact hnt hne, by rw [pk]; exact hnnt⟩
        · exact hps p hp
      · rw [bindSlots_cons]
        simpa [List.append_assoc, List.map_append] using both
    · -- `:` : end of the binders
      rename_i r0 ht0
      cases h1
      refine ⟨[], r0, n, st.ty, st.cur.nni, by omega, by rw [ht0]; simp, fun f hf => ?_, by simp [bindSlots_nil], trivial, ?_, ?_⟩
      · obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [ht0]; rw [pBinders.eq_def]; try rfl -- 4.34.1 needs the rfl; on 4.29 rw closes the goal
      · simp only [bindSlots_nil, List.map_nil, List.append_nil]
        simpa using hs1
      · simp only [bindSlots_nil, List.map_nil, List.append_nil]
        simpa using h2
    · cases h1


/-! ## the def table ↔ the spec's `DefI` list -/
/-- finished Layer-2 rows ↔ the spec's finished defs (the `defs` / `row` fields of G's `CxRel`) -/
def DRel (ds : List DefR) (dis : List DefI) : Prop :=
  ds.length = dis.length ∧ (∀ x, (findDef dis x).map (fun e => e.1) = findD ds x) ∧
  ∀ x j di, findDef dis x = some (j, di) → ∃ d, ds[j]? = some d ∧ di.params.map psCode = d.params ∧ d.res = some di.res ∧
    (∀ (i : Nat) (h : i < di.params.length), (di.params[i] = .inp ↔ FirstLs d.params i)) ∧ ∀ p ∈ di.params, p ≠ .sh .nt

/-- the kind a typed Layer-2 binding of a spec entry carries -/
theorem bdPs_toBd {e : List Nat × Nat × Ps} (h1 : e.2.2 ≠ .fuel) (h2 : psCode e.2.2 ≠ .nt) : bdPs (toBd e) = some e.2.2 := by
  obtain ⟨x, s, p⟩ := e
  cases p with
  | inp => rfl
  | fuel => exact absurd rfl h1
  | sh w =>
    simp only [psCode] at h2
    simp only [toBd, bdPs, psCode]
    cases w <;> simp_all

theorem findB_toBd (env : List (List Nat × Nat × Ps)) (x : List Nat) :
    findB (env.map toBd) x = (env.reverse.find? fun e => e.1 == x).map toBd := by
  simp only [findB, ← List.map_reverse, List.find?_map]
  rfl

/-- **G's `CxRel` at a plain body start**: bindings = the spec env (in order), no self, arm off -/
theorem cxrel_body {st : St} {dis : List DefI} {env : List (List Nat × Nat × Ps)} (hD : DRel st.defs dis)
    (hb : st.binds = env.map toBd) (he : ∀ e ∈ env, e.2.2 ≠ .fuel ∧ psCode e.2.2 ≠ .nt) (harm : st.arm = false) :
    CxRel st { defs := dis, env := env.reverse, self := none } := by
  refine ⟨fun x bd h => ?_, fun x bd h hi => ?_, fun x => ?_, hD.2.1, hD.2.2, fun _ _ e => (by cases e), fun e => (by rw [harm] at e; cases e)⟩
  · rw [hb, findB_toBd] at h
    obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [toBd]
  · rw [hb, findB_toBd] at h
    obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨x, s, p⟩ := e
    simp only [toBd, beq_iff_eq] at hi ⊢
    subst hi; rfl
  · rw [hb, findB_toBd]
    simp only [findEnv]
    cases hf : env.reverse.find? (fun e => e.1 == x) with
    | none => rfl
    | some e =>
      have hm : e ∈ env := List.mem_reverse.mp (List.mem_of_find?_eq_some hf)
      obtain ⟨h1, h2⟩ := he e hm
      simp only [Option.map_some, Option.bind_some, bdPs_toBd h1 h2]
      rfl


/-! ## the input rule of a plain def's parameters -/
/-- parameter kinds obey the input rule: the input is exactly the first List code; without an input there is no List code -/
def InpInv (Q : List Ps) : Prop :=
  (∀ i (h : i < Q.length), (Q[i] = .inp ↔ FirstLs (Q.map psCode) i)) ∧ ((∀ q ∈ Q, q ≠ .inp) → ∀ q ∈ Q, psCode q ≠ .ls)

theorem inpInv_snoc {Q : List Ps} {p : Ps} (hQ : InpInv Q)
    (hp1 : p = .inp → (∀ q ∈ Q, q ≠ .inp)) (hp2 : psCode p = .ls → p ≠ .inp → .inp ∈ Q) : InpInv (Q ++ [p]) := by
  obtain ⟨h1, h2⟩ := hQ
  refine ⟨fun i hi => ?_, fun hn q hq => ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    rw [firstLs_snoc]
    by_cases hiQ : i < Q.length
    · rw [List.getElem_append_left hiQ, h1 i hiQ]
      constructor
      · intro h; exact Or.inl ⟨by simpa using hiQ, h⟩
      · rintro (⟨_, h⟩ | ⟨e, _⟩)
        · exact h
        · simp at e; omega
    · have e : i = Q.length := by simp at hi; omega
      subst e
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero, List.length_map]
      rw [hasLs_false_iff]
      constructor
      · intro hpi
        have hnoinp := hp1 hpi
        refine Or.inr ⟨by simp, by rw [hpi]; rfl, fun j hj e => ?_⟩
        simp only [List.getElem?_map, List.length_map] at hj e
        rw [List.getElem?_eq_getElem hj] at e
        simp at e
        exact h2 hnoinp _ (List.getElem_mem hj) e
      · rintro (⟨h, _⟩ | ⟨_, hl, hno⟩)
        · simp at h
        · by_cases hpi : p = .inp
          · exact hpi
          · obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (hp2 hl hpi)
            have := (h1 j hj).mp hje
            exact absurd (by simpa [List.getElem?_map, List.getElem?_eq_getElem hj] using this.1) (hno j (by simpa using hj))
  · rcases List.mem_append.mp hq with hq | hq
    · exact h2 (fun q' hq' => hn q' (List.mem_append_left _ hq')) q hq
    · simp at hq; subst hq
      intro hl
      by_cases hpi : q = .inp
      · exact hn q (by simp [hpi]) hpi
      · obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (hp2 hl hpi)
        exact hn _ (List.mem_append_left _ (List.getElem_mem hj)) hje


theorem go_ps (p : Ps) : ∀ (s : Nat) (ns : List (List Nat)), (bindSlots.go p s ns).2.1 = List.replicate ns.length p
  | s, [] => by simp [go_nil]
  | s, x :: l => by rw [go_cons]; simp [go_ps p _ l, List.replicate_succ]

theorem inpInv_rep {Q : List Ps} {p : Ps} (hQ : InpInv Q) (k : Nat) (hk : p = .inp → k ≤ 1 ∧ ∀ q ∈ Q, q ≠ .inp)
    (hl : psCode p = .ls → p ≠ .inp → .inp ∈ Q) : InpInv (Q ++ List.replicate k p) := by
  induction k with
  | zero => simpa using hQ
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    refine inpInv_snoc (ih (fun e => ⟨by have := (hk e).1; omega, (hk e).2⟩)) (fun e q hq => ?_) (fun e1 e2 => List.mem_append_left _ (hl e1 e2))
    obtain ⟨hk1, hQ'⟩ := hk e
    rcases List.mem_append.mp hq with hq | hq
    · exact hQ' q hq
    · have : k = 0 := by omega
      subst this; simp at hq

/-- **input rule**: under fix J, the parameter kinds of a binder list obey `InpInv` -/
theorem bindSlots_inpInv : ∀ (g : List (List (List Nat) × TyR)) (u : Bool) (s : Nat) (Q : List Ps), InpInv Q →
    u = Q.any (· == .inp) → FixJ u g → (∀ x ∈ g, x.2 ≠ .sh .ls) → InpInv (Q ++ (bindSlots s u g).2.1)
  | [], u, s, Q, hQ, _, _, _ => by simpa [bindSlots_nil] using hQ
  | (ns, t) :: g, u, s, Q, hQ, hu, hF, hT => by
    rw [bindSlots_cons, ← List.append_assoc, go_ps]
    have ht : t ≠ .sh .ls := hT (ns, t) (by simp)
    obtain ⟨hF1, hF2⟩ := hF
    have h1 : InpInv (Q ++ List.replicate ns.length (pickPs u (ns.length == 1) t).1) := by
      apply inpInv_rep hQ
      · intro e
        cases t with
        | sh w => simp [pickPs] at e
        | lst =>
          cases u <;> cases h : (ns.length == 1) <;> simp [pickPs, h] at e
          refine ⟨by simp at h; omega, fun q hq hqi => ?_⟩
          have : Q.any (· == .inp) = true := List.any_eq_true.mpr ⟨q, hq, by simp [hqi]⟩
          rw [← hu] at this; cases this
      · intro hl hni
        cases t with
        | sh w => simp [pickPs, psCode] at hl; subst hl; exact absurd rfl ht
        | lst =>
          have hu1 : u = true := by
            cases h : (ns.length == 1)
            · exact hF1 rfl (by simpa using h)
            · cases u
              · simp [pickPs, h] at hni
              · rfl
          rw [hu1] at hu
          obtain ⟨q, hq, hqe⟩ := List.any_eq_true.mp hu.symm
          simp at hqe; subst hqe; exact hq
    refine bindSlots_inpInv g _ _ _ h1 ?_ hF2 (fun x hx => hT x (by simp [hx]))
    rw [pick_used, List.any_append, ← hu]
    cases ns with
    | nil =>
      cases t with
      | sh w => simp [pickPs]
      | lst => cases u <;> simp [pickPs]
    | cons y l => simp [List.any_replicate]


theorem findD_snoc' (l : List DefR) (d : DefR) (x : List Nat) :
    findD (l ++ [d]) x = if d.name = x then some l.length else findD l x := by
  unfold findD
  rw [List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  rw [List.findIdx?_cons]
  by_cases hd : d.name = x
  · simp [hd]
  · simp only [hd, beq_iff_eq, if_false, Option.map_map]
    simp only [List.length_append, List.length_singleton]
    cases hf : List.findIdx? (fun d => d.name == x) l.reverse with
    | none => simp
    | some i =>
      have := (List.findIdx?_eq_some_iff_getElem.mp hf).1
      simp at this ⊢; omega

theorem findDef_snoc (l : List DefI) (d : DefI) (x : List Nat) :
    findDef (l ++ [d]) x = (findDef l x).or (if d.name = x then some (l.length, d) else none) := by
  unfold findDef
  rw [List.zipIdx_append, List.find?_append]
  cases hf : l.zipIdx.find? (fun e => e.1.name == x) with
  | some e => simp
  | none => by_cases hd : d.name = x <;> simp [hd]

/-- the def table after `defClose`: a fresh row whose spec `DefI` matches -/
theorem drel_snoc {ds : List DefR} {dis : List DefI} (hD : DRel ds dis) {cur : DefR} {di : DefI} (hfr : findD ds cur.name = none)
    (hn : di.name = cur.name) (hp : di.params.map psCode = cur.params) (hr : cur.res = some di.res)
    (hi : ∀ (i : Nat) (h : i < di.params.length), (di.params[i] = .inp ↔ FirstLs cur.params i)) (hnt : ∀ p ∈ di.params, p ≠ .sh .nt) :
    DRel (ds ++ [cur]) (dis ++ [di]) := by
  obtain ⟨hl, hf, hrow⟩ := hD
  have hfr' : findDef dis cur.name = none := by
    have := hf cur.name; rw [hfr] at this; cases h : findDef dis cur.name <;> simp_all
  refine ⟨by simp [hl], fun x => ?_, fun x j d' h => ?_⟩
  · rw [findDef_snoc, findD_snoc', hn]
    by_cases hx : cur.name = x
    · subst hx; simp [hfr', hl]
    · rw [← hf x]; cases findDef dis x <;> simp [hx]
  · rw [findDef_snoc, hn] at h
    cases h1 : findDef dis x with
    | some e =>
      have h' : findDef dis x = some (j, d') := by rw [h1] at h ⊢; simpa using h
      obtain ⟨d, hd, r1, r2, r3, r4⟩ := hrow x _ _ h'
      have hj : j < ds.length := (List.getElem?_eq_some_iff.mp hd).1
      exact ⟨d, by rw [List.getElem?_append_left hj]; exact hd, r1, r2, r3, r4⟩
    | none =>
      rw [h1] at h
      by_cases hx : cur.name = x
      · simp [hx] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨cur, by rw [← hl]; simp, hp, hr, hi, hnt⟩
      · simp [hx] at h

end ParRun
