/- Nano/V2Self/Proof/Parser/ParRunExpr: Layer 2 → ParSpec for EXPRESSIONS (box B).  Frame inversions and the binary-operator loop. -/
import Nano.V2Self.Proof.Parser.ParRunAtom
import Nano.V2Self.Proof.Parser.ParTreeOK
import Nano.V2Self.Proof.Parser.ParSpecTail
import Nano.V2Self.Proof.Parser.ParRunTy
namespace ParRun
open ParSpec

/-- the deferred validation (v209 at the next `defs`) holds for every node of `v` -/
def VT (ds : List DefR) (v : RN) : Prop := ∀ u ∈ nodes v, nodeOK ds u = true

/-- the effect of an expression-like run on the state: one value replaces `base`'s top part; tables unchanged -/
structure Post (st st' : St) (base : List RN) (v : RN) : Prop where
  vals : st'.vals = v :: base
  binds : st'.binds = st.binds
  defs : st'.defs = st.defs
  cur : st'.cur = st.cur
  arm : st'.arm = st.arm
  all : st'.all = st.all
  toks : st'.toks.length ≤ st.toks.length
  nx : st.nx ≤ st'.nx
  out : st'.out = st.out

theorem binLoop_inv {m st k st'} (h : stepF (.binLoop m) st = some (k, st')) :
    (k = [] ∧ st' = st ∧ ∀ t r op p, st.toks = .k t :: r → opInfo t = some (op, p) → p < m) ∨
    (∃ t r op p top rest, st.toks = .k t :: r ∧ opInfo t = some (op, p) ∧ m ≤ p ∧ st.vals = top :: rest ∧ top.pend = false ∧
      st' = { st with toks := r } ∧
      ((t = 28 ∨ t = 29) ∧ k = [.shiftNum op, .binLoop m] ∨ ¬(t = 28 ∨ t = 29) ∧ k = [.expr (p + 1) 2, .mkBin op, .binLoop m])) := by
  simp only [stepF] at h
  split at h
  · rename_i t r ht
    split at h
    · rename_i hop
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, rfl, fun t' r' op p he ho => by rw [ht] at he; cases he; rw [hop] at ho; cases ho⟩
    · rename_i op p hop
      split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h
        exact Or.inl ⟨rfl, rfl, fun t' r' op' p' he ho => by rw [ht] at he; cases he; rw [hop] at ho; cases ho; assumption⟩
      · rename_i hp
        split at h
        · rename_i top rest hv
          split at h
          · simp at h
          · rename_i hpend
            split at h
            · simp at h; obtain ⟨rfl, rfl⟩ := h
              exact Or.inr ⟨t, r, op, p, top, rest, ht, hop, by omega, hv, by simpa using hpend, rfl, Or.inl ⟨by assumption, rfl⟩⟩
            · simp at h; obtain ⟨rfl, rfl⟩ := h
              exact Or.inr ⟨t, r, op, p, top, rest, ht, hop, by omega, hv, by simpa using hpend, rfl, Or.inr ⟨by assumption, rfl⟩⟩
        · simp at h
  · simp at h; obtain ⟨rfl, rfl⟩ := h
    rename_i hne
    exact Or.inl ⟨rfl, rfl, fun t r op p he _ => absurd he (hne t r)⟩


theorem shiftNum_inv {op st k st'} (h : stepF (.shiftNum op) st = some (k, st')) :
    ∃ v r, st.toks = .num v :: r ∧ k = [.mkBin op] ∧ st' = leaf { st with toks := r } 1 v 0 .uw := by
  simp only [stepF] at h
  split at h
  · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨_, _, ‹_›, rfl, rfl⟩
  · simp at h

theorem mkBin_inv {op st k st'} (h : stepF (.mkBin op) st = some (k, st')) :
    ∃ y x rest, st.vals = y :: x :: rest ∧ x.sh = some .uw ∧ y.sh = some .uw ∧ k = [] ∧
      st' = { st with vals := RN.mk 3 op 0 (some .uw) false [x, y] :: rest, arena := st.arena ++ [RN.mk 3 op 0 (some .uw) false [x, y]] } := by
  simp only [stepF] at h
  split at h
  · rename_i y x rest hv
    split at h
    · obtain ⟨st2, hm, he⟩ := Option.map_eq_some_iff.mp h
      simp at he; obtain ⟨rfl, rfl⟩ := he
      obtain ⟨_, rfl⟩ := mkNode_inv hm
      refine ⟨y, x, rest, hv, ‹_ ∧ _›.1, ‹_ ∧ _›.2, rfl, ?_⟩
      simp [hv]
    · simp at h
  · simp at h

theorem CxRel.transport {st st' : St} {cx : Cx} (h : CxRel st cx) (hb : st'.binds = st.binds) (hd : st'.defs = st.defs)
    (hcu : st'.cur = st.cur) (har : st'.arm = st.arm) : CxRel st' cx := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨by rw [hb]; exact h1, by rw [hb]; exact h2, by rw [hb]; exact h3, by rw [hd]; exact h4, by rw [hd]; exact h5, h6,
    by rw [hcu, har]; exact h7⟩

theorem TyRel.notInp {v : RN} {ty : Ty} (h : TyRel v ty) (hu : v.sh = some .uw) (hb : ty ≠ .bot) : v.isInp = false := by
  cases ty with
  | s s =>
    cases hi : v.isInp
    · rfl
    · obtain ⟨l, r, rfl⟩ := h.2.1 hi; rw [h.1] at hu; cases hu
  | lit => exact h.2
  | inp => rw [h.2] at hu; cases hu
  | bot => exact absurd rfl hb

theorem TyRel.isU {v : RN} {ty : Ty} (h : TyRel v ty) (hu : v.sh = some .uw) (hp : v.pend = false) : isU ty = true := by
  cases ty with
  | s s => rw [h.1] at hu; cases hu; rfl
  | lit => rfl
  | inp => rw [h.2] at hu; cases hu
  | bot => have := h; simp [TyRel] at this; rw [this] at hp; cases hp

theorem pLoop_stop {f cx m a ta ts nx} (hf : 1 ≤ f) (hs : ∀ t r op p, ts = .k t :: r → opInfo t = some (op, p) → p < m) :
    pLoop f cx m a ta ts nx = some (a, ta, ts, nx) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [pLoop.eq_def]; simp only
  split
  · rename_i t r
    split
    · rw [if_pos (hs t r _ _ rfl ‹opInfo _ = some _›)]
    · rfl
  · rfl


def ShNN (o : Option Sh) : Prop := ∃ s, o = some s ∧ s.nnt = true

/-- the tables hold no nested Nat -/
def CxNN (st : St) : Prop := (∀ bd ∈ st.binds, ShNN bd.sh) ∧ (∀ d ∈ rows st, ShNN d.res ∧ ∀ p ∈ d.params, p.nnt = true)

theorem CxNN.transport {st st' : St} (h : CxNN st) (hb : st'.binds = st.binds) (hd : st'.defs = st.defs) (hc : st'.cur = st.cur) :
    CxNN st' := by
  unfold CxNN ParRun.rows at *; rw [hb, hd, hc]; exact h

/-- a tail CONTINUE inside `v` makes `v` pending (what `binLoop` / `mkPair` test instead of the spec's tail flag) -/
def PT (v : RN) : Prop := v.toNd.tailCont = true → v.pend = true

/-- the operator loop stopped: no operator of precedence ≥ m follows -/
def Stop (m : Nat) (ts : List Tok) : Prop := ∀ t r op p, ts = .k t :: r → opInfo t = some (op, p) → p < m

/-- the operand parse (`expr m 2` ↔ `pBin f cx false m`) for runs of length `n` -/
def BinSpec (n : Nat) : Prop := ∀ m ks st fin cx, StarN n (.expr m 2 :: ks, st) ([], fin) → CxRel st cx → CxNN st →
  ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ Stop m st'.toks ∧
    ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ PT v ∧
      ∀ f, 4 * st.toks.length + 3 ≤ f → pBin f cx false m st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx))

/-- the operator loop (`binLoop m` with `a` on top ↔ `pLoop f cx m a.toNd ta`) -/
def LoopSpec (n : Nat) : Prop := ∀ m ks st fin cx a rest ta, StarN n (.binLoop m :: ks, st) ([], fin) → st.vals = a :: rest →
  CxRel st cx → CxNN st → ShNN a.sh → (VT (rows st) a → TyRel a ta ∧ PT a) →
  ∃ v st' n', n' < n ∧ Post st st' rest v ∧ (∀ u ∈ nodes a, u ∈ nodes v) ∧ StarN n' (ks, st') ([], fin) ∧ Stop m st'.toks ∧
    ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ PT v ∧
      ∀ f, 4 * st.toks.length + 1 ≤ f → pLoop f cx m a.toNd ta st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx))

theorem binNode_toNd {op : Nat} {x y : RN} (hx : x.isInp = false) (hy : y.isInp = false) :
    (RN.mk 3 op 0 (some .uw) false [x, y]).toNd = .bin op x.toNd y.toNd := by
  rw [RN.toNd_mk]; simp [RN.toNdL_cons, RN.toNdL, hx, hy]

theorem PT_bin (op : Nat) (x y : RN) : PT (RN.mk 3 op 0 (some .uw) false [x, y]) := by
  intro h
  rw [RN.toNd_mk] at h
  simp only [show ¬ (3 = 9 ∧ op < 4) by omega, if_false, show (3 : Nat) ≠ 1 by omega, show (3 : Nat) ≠ 2 by omega, if_true] at h
  generalize RN.toNdL [x, y] = l at h
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp [Nd.tailCont] at h

theorem VT.kid {ds : List DefR} {t a b : Nat} {s : Option Sh} {p : Bool} {ks : List RN} {k : RN} (h : VT ds (.mk t a b s p ks))
    (hk : k ∈ ks) : VT ds k := fun u hu => h u (kid_nodes_sub hk hu)

theorem loop_sound : ∀ n, (∀ n' < n, BinSpec n') → LoopSpec n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihL =>
  intro IHB m ks st fin cx a rest ta h hv hc hnn hna ha
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  rcases binLoop_inv hs with ⟨hk0, hst, hlt⟩ | ⟨t, r, op, p, top, rest', ht, hop, hmp, hv', hpend, rfl, hk⟩
  · -- no operator of precedence ≥ m: the loop returns `a`
    rw [hk0, hst] at h1
    refine ⟨a, st, n, by omega, ⟨hv, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, rfl⟩, fun u hu => hu, h1, hlt, hna,
      fun hvt => ⟨ta, (ha hvt).1, (ha hvt).2, fun f hf => ?_⟩⟩
    exact pLoop_stop (by omega) hlt
  · rw [hv] at hv'; injection hv' with htop hrest; subst htop hrest
    rcases hk with ⟨hsh, rfl⟩ | ⟨hsh, rfl⟩
    · -- shift by a numeral
      match n, h1 with
      | 0, h1 => exact absurd h1.zero_nil.1 (by simp)
      | n + 1, h1 =>
      obtain ⟨k2, st2, hs2, h2⟩ := h1.head
      obtain ⟨kv, r', hr, rfl, rfl⟩ := shiftNum_inv hs2
      simp only at hr; subst hr
      match n, h2 with
      | 0, h2 => exact absurd h2.zero_nil.1 (by simp)
      | n + 1, h2 =>
      obtain ⟨k3, st3, hs3, h3⟩ := h2.head
      obtain ⟨y, x, rest3, hv3, hx, hy, rfl, rfl⟩ := mkBin_inv hs3
      simp only [leaf, hv, List.cons.injEq] at hv3
      obtain ⟨rfl, rfl, rfl⟩ := hv3
      simp only [List.nil_append] at h3
      have hb : TyRel (RN.mk 3 op 0 (some .uw) false [a, RN.mk 1 kv 0 (some .uw) false []]) (.s .uw) := ⟨rfl, by simp [RN.isInp, RN.tag], by simp [RN.tag]⟩
      obtain ⟨v, st', n', hn', hp, hsub, hrun, hstop, hnv, hspec⟩ := ihL n (by omega) (fun n'' hn'' => IHB n'' (by omega)) m ks _ fin cx _ _ _ h3 rfl
        (CxRel.transport hc rfl rfl rfl rfl) (CxNN.transport hnn rfl rfl rfl) ⟨.uw, rfl, rfl⟩
        (fun _ => ⟨hb, PT_bin _ _ _⟩)
      refine ⟨v, st', n', by omega, ⟨hp.vals, hp.binds, hp.defs, hp.cur, hp.arm, hp.all, ?_, hp.nx, hp.out⟩,
        fun u hu => hsub u (kid_nodes_sub (List.mem_cons_self ..) hu), hrun, hstop, hnv, fun hvt => ?_⟩
      · have := hp.toks; simp [ht, leaf] at this ⊢; omega
      obtain ⟨ty, hty, hpt, hf⟩ := hspec hvt
      refine ⟨ty, hty, hpt, fun f hf' => ?_⟩
      have hva : VT (rows st) a := fun u hu => hvt u (hsub u (kid_nodes_sub (List.mem_cons_self ..) hu))
      have hta := (ha hva).1
      have hu := hta.isU hx hpend
      have hni : a.isInp = false := by
        cases ta with
        | bot => have := hta; simp [TyRel] at this; rw [this] at hpend; cases hpend
        | _ => exact hta.notInp hx (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [ht, pLoop.eq_def]; simp only [hop]
      rw [if_neg (by omega), if_pos hu, if_pos hsh]
      have := hf g (by simp [ht, leaf] at hf' ⊢; omega)
      rw [binNode_toNd hni rfl] at this
      simpa [RN.toNd_mk, leaf] using this
    · -- operator with a parsed right operand
      simp only [List.cons_append, List.nil_append] at h1
      obtain ⟨y, st2, n2, hn2, hp2, hlt2, h2, _, _, hspec2⟩ :=
        IHB n (by omega) (p + 1) (.mkBin op :: .binLoop m :: ks) _ fin cx h1 (CxRel.transport hc rfl rfl rfl rfl) (CxNN.transport hnn rfl rfl rfl)
      match n2, h2 with
      | 0, h2 => exact absurd h2.zero_nil.1 (by simp)
      | n2 + 1, h2 =>
      obtain ⟨k3, st3, hs3, h3⟩ := h2.head
      obtain ⟨y', x, rest3, hv3, hx, hy, hk3, hst3⟩ := mkBin_inv hs3
      subst hk3
      rw [hp2.vals] at hv3
      simp only [hv, List.cons.injEq] at hv3
      obtain ⟨rfl, rfl, rfl⟩ := hv3
      simp only [List.nil_append] at h3
      have hb : TyRel (RN.mk 3 op 0 (some .uw) false [a, y]) (.s .uw) := ⟨rfl, by simp [RN.isInp, RN.tag], by simp [RN.tag]⟩
      have hc3 : CxRel st3 cx := CxRel.transport hc (by rw [hst3]; exact hp2.binds) (by rw [hst3]; exact hp2.defs) (by rw [hst3]; exact hp2.cur) (by rw [hst3]; exact hp2.arm)
      have hv3' : st3.vals = RN.mk 3 op 0 (some .uw) false [a, y] :: rest := by rw [hst3]
      obtain ⟨v, st', n', hn', hp, hsub, hrun, hstop, hnv, hspec⟩ :=
        ihL n2 (by omega) (fun n'' hn'' => IHB n'' (by omega)) m ks _ fin cx _ _ _ h3 hv3' hc3
          (CxNN.transport hnn (by rw [hst3]; exact hp2.binds) (by rw [hst3]; exact hp2.defs) (by rw [hst3]; exact hp2.cur))
          ⟨.uw, rfl, rfl⟩ (fun _ => ⟨hb, PT_bin _ _ _⟩)
      have hrows : rows st3 = rows st := by simp [hst3, rows, hp2.defs, hp2.cur]
      rw [hrows] at hspec
      have hsubb : ∀ u ∈ nodes (RN.mk 3 op 0 (some .uw) false [a, y]), u ∈ nodes v := hsub
      refine ⟨v, st', n', by omega, ⟨hp.vals, by rw [hp.binds, hst3]; exact hp2.binds, by rw [hp.defs, hst3]; exact hp2.defs,
        by rw [hp.cur, hst3]; exact hp2.cur, by rw [hp.arm, hst3]; exact hp2.arm, by rw [hp.all, hst3]; exact hp2.all, ?_, ?_, by rw [hp.out, hst3]; exact hp2.out⟩,
        fun u hu => hsubb u (kid_nodes_sub (List.mem_cons_self ..) hu), hrun, hstop, hnv, fun hvt => ?_⟩
      · have h1' := hp.toks; have h2' := hp2.toks; rw [hst3] at h1'; simp [ht] at h1' h2' hlt2 ⊢; omega
      · have h1' := hp.nx; have h2' := hp2.nx; rw [hst3] at h1'; simp at h1' h2' ⊢; omega
      obtain ⟨ty, hty, hpt, hf⟩ := hspec hvt
      refine ⟨ty, hty, hpt, fun f hf' => ?_⟩
      have hvb : VT (rows st) (RN.mk 3 op 0 (some .uw) false [a, y]) := fun u hu => hvt u (hsubb u hu)
      have hta := (ha (hvb.kid (List.mem_cons_self ..))).1
      have hrows1 : rows ({ st with toks := r } : St) = rows st := rfl
      obtain ⟨tyy, htyy, _, hfy⟩ := hspec2 (by rw [hrows1]; exact hvb.kid (by simp))
      have hu := hta.isU hx hpend
      have hni : a.isInp = false := by
        cases ta with
        | bot => have := hta; simp [TyRel] at this; rw [this] at hpend; cases hpend
        | _ => exact hta.notInp hx (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      have hpy := hfy g (by simp [ht] at hf' ⊢; omega)
      have hnb : tyy ≠ .bot := (nobot g).2.1 _ _ _ _ _ hpy
      have huy : isU tyy = true := by
        cases tyy with
        | s s => rw [htyy.1] at hy; cases hy; rfl
        | lit => rfl
        | inp => rw [htyy.2] at hy; cases hy
        | bot => exact absurd rfl hnb
      have hniy : y.isInp = false := htyy.notInp hy hnb
      rw [ht, pLoop.eq_def]; simp only [hop]
      rw [if_neg (by omega), if_pos hu, if_neg hsh]
      simp only at hpy
      rw [hpy]; simp only [Option.bind_some, huy, if_true]
      have := hf g (by rw [hst3]; simp [ht] at hf' hlt2 ⊢; omega)
      rw [hst3] at this
      rw [binNode_toNd hni hniy] at this
      simpa using this

end ParRun
