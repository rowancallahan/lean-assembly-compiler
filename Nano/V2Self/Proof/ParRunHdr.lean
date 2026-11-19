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

end ParRun
