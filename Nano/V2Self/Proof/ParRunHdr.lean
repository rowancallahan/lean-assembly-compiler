/- Nano/V2Self/Proof/ParRunHdr: Layer-2 def headers ↔ ParSpec (parser lead), pure.
* `group_spec`: the `group` frame collects the identifiers of a binder group exactly as `pBinders.ids`, as untyped placeholders. -/
import Nano.V2Self.Proof.ParRunDefs
import Nano.V2Self.Proof.ParRunRow
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
      StarN n' (.tyAtom :: .rparen :: .assign a (st.binds.length + ns.length - a) :: .binders :: ks,
        { st with toks := r, binds := st.binds ++ ns.map phB }) ([], fin) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro a ks st fin h
  match n, h with
  | n + 1, h =>
    obtain ⟨k, st1, h1, h2⟩ := h.head
    simp only [stepF] at h1
    split at h1
    · rename_i x r ht
      cases h1
      obtain ⟨ns, r', n', hn, hi, ha, h3⟩ := ih n (by omega) h2
      refine ⟨x :: ns, r', n', by omega, ?_, ?_, ?_⟩
      · rw [ht, ids_id]; simp only at hi; rw [hi]; rfl
      · simp at ha ⊢; omega
      · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.append_assoc,
          List.singleton_append, List.cons_append, List.nil_append] at h3 ⊢
        have e1 : st.binds.length + 1 + ns.length = st.binds.length + (ns.length + 1) := by omega
        rw [e1] at h3
        exact h3
    · rename_i r ht
      split at h1
      · cases h1
        rename_i hlt
        exact ⟨[], r, n, by omega, by rw [ht, ids_k], by simpa using hlt, by simpa using h2⟩
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
    ∃ n', n' < n ∧ (ns ≠ [] → trRes t ≠ .nt) ∧
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
      exact ⟨n, by omega, fun e => absurd rfl e, by rw [e]; simpa using h2⟩
  | cons x ns ih =>
    intro n a ks st fin P h hty hb ha hu hsz
    match n, h with
    | n + 1, h =>
      obtain ⟨k, st1, h1, h2⟩ := h.head
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
      obtain ⟨n', hn', _, h3⟩ := ih n (a + 1) (P ++ [toBd (x, st.nx, (pickPs used (sz == 1) t).1)]) h2
        rfl rfl (by simp [ha])
        (fun e1 e2 => absurd (List.eq_nil_of_length_eq_zero (by have := hsz e1; rw [List.length_cons] at this; omega)) e2)
        (fun e1 => by have := hsz e1; rw [List.length_cons] at this; omega)
      refine ⟨n', by omega, fun _ => hnt, ?_⟩
      rw [go_cons]
      rw [hn1] at h3
      generalize (pickPs used (sz == 1) t).1 = p at pk pf h3 ⊢
      rw [← pk] at h3 hty
      cases p with
      | inp => simpa [Ps.width, toBd, List.append_assoc, hty] using h3
      | fuel => exact absurd rfl pf
      | sh s => simpa [Ps.width, psCode, toBd, List.append_assoc, Nat.add_assoc, Nat.add_comm 1, hty] using h3


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


/-- **binder list** `(a b : T) (c : U) … :` ↔ `pBinders` + `bindSlots` from the current slot / input flag -/
theorem binders_spec : ∀ (n : Nat) {ks : List Frame} {st fin : St} (b : Bool), StarN n (.binders :: ks, st) ([], fin) →
    ∃ groups r n' ty' nni', n' < n ∧
      (∀ f, 3 * st.toks.length + 3 ≤ f → pBinders f b st.toks = some (groups, .k 8 :: r)) ∧
      (∀ p ∈ (bindSlots st.nx (st.binds.any Bd.inp) groups).2.1, p ≠ .fuel ∧ psCode p ≠ .nt ∧ (psCode p).nnt = true) ∧
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
    obtain ⟨k, st1, h1, h2⟩ := h.head
    simp only [stepF] at h1
    split at h1
    · -- `(` : a group
      rename_i r0 ht0
      cases h1
      simp only [List.singleton_append] at h2
      obtain ⟨ns, r1, n2, hn2, hids, hlt, h3⟩ := group_spec n h2
      have hne : ns ≠ [] := by intro e; subst e; simp at hlt
      obtain ⟨t, r2, n3, hn3, hl2, hpTy, h4, hnnt⟩ := (ty_sound n2).1 h3
      dsimp only at hl2 hpTy
      have htl : t ≠ .sh .ls := (pTy_noLs (2 * r1.length + 2)).2 r1 t r2 (hpTy _ (Nat.le_refl _))
      match n3, h4 with
      | n3 + 1, h4 =>
      obtain ⟨k5, st5, h5, h6⟩ := h4.head
      simp only [stepF, St.withTy] at h5
      obtain ⟨r4, rfl⟩ : ∃ r4, r2 = .k 7 :: r4 := by
        match r2, h5 with
        | .k 7 :: r4, _ => exact ⟨r4, rfl⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl⟩ := h5
      have hsz : st.binds.length + ns.length - st.binds.length = ns.length := by omega
      simp only [List.nil_append, hsz] at h6
      obtain ⟨n4, hn4, hnt, h7⟩ := assign_spec htl (used := st.binds.any Bd.inp) ns n3 st.binds.length st.binds h6 rfl rfl rfl
        (fun _ _ => rfl) (fun e => by omega)
      obtain ⟨g, r, n5, ty', nni', hn5, hpB, hps, h8⟩ := ih n4 (by omega) false h7
      dsimp only at hpB hps h8
      have hused : (st.binds ++ List.map toBd (bindSlots.go (pickPs (st.binds.any Bd.inp) (ns.length == 1) t).1 st.nx ns).1).any
          Bd.inp = (pickPs (st.binds.any Bd.inp) (ns.length == 1) t).2 := by
        rw [List.any_append, any_go _ _ _ hne, pick_used]
      rw [hused] at hps h8
      refine ⟨(ns, t) :: g, r, n5, ty', nni', by omega, ?_, ?_, ?_⟩
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
        simpa [List.append_assoc, List.map_append] using h8
    · -- `:` : end of the binders
      rename_i r0 ht0
      cases h1
      refine ⟨[], r0, n, st.ty, st.cur.nni, by omega, fun f hf => ?_, by simp [bindSlots_nil], ?_⟩
      · obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [ht0]; rw [pBinders.eq_def]
      · simp only [bindSlots_nil, List.map_nil, List.append_nil]
        simpa using h2
    · cases h1

end ParRun
