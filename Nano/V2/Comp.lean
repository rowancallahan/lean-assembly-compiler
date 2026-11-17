import Nano.V2.Inp
/- nano v2 increment 3 (products): **`cE_ok`**, the expression compiler `cE` (Nano/V2/Gen.lean) is correct on the
LOOP-FREE, BUFFER-FREE fragment `Ex.Pure` (words, `bin`, `ite`, `let`, pairs, `fst`/`snd`, consuming `split`, input
reads), on the abstract machine of Nano/V2/Sem.lean.  A value is its words side by side (`Val.flat`); the compile-time
environment entry `(τ, p)` holds the variable's `τ.size` words from absolute slot `p` (`EnvRep`). -/
namespace Nano.V2B

/-- increment 3's fragment: no buffers, no loops -/
def Ex.Pure : Ex → Bool
  | .lit _ => true
  | .var _ => true
  | .isize => true
  | .bin _ a b => a.Pure && b.Pure
  | .ite _ a b t e => a.Pure && b.Pure && t.Pure && e.Pure
  | .let_ v b => v.Pure && b.Pure
  | .pair a b => a.Pure && b.Pure
  | .fst e => e.Pure
  | .snd e => e.Pure
  | .split e b => e.Pure && b.Pure
  | .iget i => i.Pure
  | _ => false

/-- a value's run-time words -/
def Val.flat : Val → List UInt64
  | .wd x => [x]
  | .bf _ => []
  | .pr a b => a.flat ++ b.flat

/-- buffer-free typing of values -/
def Val.HasTy : Val → Ty → Prop
  | .wd _, .w => True
  | .pr a b, .prod τ σ => a.HasTy τ ∧ b.HasTy σ
  | _, _ => False

theorem Val.HasTy.len : ∀ {v : Val} {τ : Ty}, v.HasTy τ → v.flat.length = τ.size
  | .wd _, .w, _ => rfl
  | .pr _ _, .prod _ _, ⟨ha, hb⟩ => by simp [Val.flat, Ty.size, ha.len, hb.len]
  | .wd _, .buf, h => h.elim
  | .wd _, .prod _ _, h => h.elim
  | .bf _, _, h => h.elim
  | .pr _ _, .w, h => h.elim
  | .pr _ _, .buf, h => h.elim

theorem Val.HasTy.w : ∀ {v : Val}, v.HasTy .w → v = .wd v.word
  | .wd _, _ => rfl
  | .bf _, h => h.elim
  | .pr _ _, h => h.elim

theorem Val.HasTy.prod : ∀ {v : Val} {τ σ : Ty}, v.HasTy (.prod τ σ) → v = .pr v.fst v.snd ∧ v.fst.HasTy τ ∧ v.snd.HasTy σ
  | .pr _ _, _, _, h => ⟨rfl, h⟩
  | .wd _, _, _, h => h.elim
  | .bf _, _, _, h => h.elim

/-- the compile-time environment describes the stack `L` and the values `vs` -/
def EnvRep (L : List UInt64) : List (Ty × Nat) → List Val → Prop
  | [], [] => True
  | (τ, p) :: env, v :: vs => v.HasTy τ ∧ p + τ.size ≤ L.length ∧ (L.drop p).take τ.size = v.flat ∧ EnvRep L env vs
  | _, _ => False

theorem EnvRep.ext {L : List UInt64} (M : List UInt64) :
    ∀ {env : List (Ty × Nat)} {vs : List Val}, EnvRep L env vs → EnvRep (L ++ M) env vs
  | [], [], _ => trivial
  | (τ, p) :: _, _ :: _, ⟨h1, h2, h3, h4⟩ => by
    refine ⟨h1, by simp; omega, ?_, EnvRep.ext M h4⟩
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]; exact h3
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem EnvRep.get {L : List UInt64} :
    ∀ {env : List (Ty × Nat)} {vs : List Val} {i : Nat} {τ : Ty} {p : Nat}, EnvRep L env vs → env[i]? = some (τ, p) →
      (vs.getD i (.wd 0)).HasTy τ ∧ p + τ.size ≤ L.length ∧ (L.drop p).take τ.size = (vs.getD i (.wd 0)).flat
  | [], _, _, _, _, _, h => by simp at h
  | (_, _) :: _, _ :: _, 0, _, _, ⟨h1, h2, h3, _⟩, h => by
    simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨h1, h2, h3⟩
  | (_, _) :: _, _ :: _, i + 1, _, _, ⟨_, _, _, h4⟩, h => by
    simp only [List.getElem?_cons_succ] at h; simpa using EnvRep.get h4 h
  | _ :: _, [], _, _, _, h, _ => h.elim

/-- the new top entry of an extended stack -/
theorem EnvRep.top {L V : List UInt64} {env : List (Ty × Nat)} {vs : List Val} {v : Val} {τ : Ty}
    (he : EnvRep L env vs) (hv : v.HasTy τ) (hV : v.flat = V) : EnvRep (L ++ V) ((τ, L.length) :: env) (v :: vs) := by
  subst hV
  have hl := hv.len
  refine ⟨hv, by simp; omega, ?_, he.ext _⟩
  rw [List.drop_left, ← hl, List.take_length]

theorem ROp.ofOp_eval (o : Op) (x y : UInt64) : (ROp.ofOp o).eval x y = o.eval x y := by
  cases o <;> simp only [ROp.ofOp, ROp.eval, Op.eval]
  · apply UInt64.toBitVec_inj.mp; simp [UInt64.toBitVec_shiftLeft]
  · apply UInt64.toBitVec_inj.mp; simp [UInt64.toBitVec_shiftRight]

theorem flat_ite (b : Bool) (u v : Val) : (if b then u else v).flat = if b then u.flat else v.flat := by
  cases b <;> rfl

/-! ## the induction -/

/-- what `cE_ok` proves of one expression -/
def Good (c : Cfg) (h : Nat) (code : SC) (τ : Ty) (L : List UInt64) (v : Val) : Prop :=
  v.HasTy τ ∧ ∀ s, Stk c s h L → InpRep c s → ∃ r, SC.Ex c code s r ∧ Post c s h L v.flat r

theorem cE_ok {c : Cfg} {h : Nat} (hc : c.Good) :
    ∀ (e : Ex) (env : List (Ty × Nat)) (vals : List Val) (code : SC) (τ : Ty) (L : List UInt64),
      e.Pure = true → cE env L.length e = some (code, τ) → EnvRep L env vals →
      Good c h code τ L (den (inpW c) e vals)
  | .lit n, env, vals, code, τ, L, _, he, _ => by
    simp only [cE, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨by simp [den, Val.HasTy], fun s hs _ => by simpa [den, Val.flat] using lit_ok hc hs n⟩
  | .var i, env, vals, code, τ, L, _, he, hr => by
    unfold cE at he
    split at he
    · rename_i τ' p hi
      split at he
      · rename_i hb
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨h1, h2, h3⟩ := hr.get hi
        simp only [den]
        refine ⟨h1, fun s hs _ => ?_⟩
        have := varC_ok hc (L.length - 1 - p) (by unfold Lim at hb; omega) τ'.size L s hs (by omega) (by omega)
        rw [show seg L (L.length - 1 - p) τ'.size = (L.drop p).take τ'.size by
          unfold seg; congr 2; omega, h3] at this
        exact this
      · simp at he
    · simp at he
  | .isize, env, vals, code, τ, L, _, he, _ => by
    simp only [cE, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨by simp [den, Val.HasTy], fun s hs hin => by simpa [den, Val.flat] using isize_node hc hs hin⟩
  | .iget i, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ci hi
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [Ex.Pure] at hp
      obtain ⟨t1, r1⟩ := cE_ok hc i env vals ci .w L hp hi hr
      refine ⟨by simp [den, Val.HasTy], fun s hs hin => ?_⟩
      have r := r1 s hs hin
      rw [t1.w] at r
      simpa [den, Val.flat] using iget_node hc hs hin r
    · simp at he
  | .bin o a b, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ca cb ha hb
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [Ex.Pure, Bool.and_eq_true] at hp
      obtain ⟨ta, ra⟩ := cE_ok hc a env vals ca .w L hp.1 ha hr
      let x := (den (inpW c) a vals).word
      have hb' : cE env (L ++ [x]).length b = some (cb, .w) := by simpa using hb
      obtain ⟨tb, rb⟩ := cE_ok hc b env vals cb .w _ hp.2 hb' (hr.ext _)
      refine ⟨by simp [den, Val.HasTy], fun s hs hin => ?_⟩
      have ra' := ra s hs hin
      rw [ta.w] at ra'
      have := bin_node hc hs (ROp.ofOp o) ra' (fun s1 hs1 k1 => by
        have rb' := rb s1 hs1 (hin.keep k1); rw [tb.w] at rb'; exact rb')
      simpa [den, Val.flat, ROp.ofOp_eval] using this
    · simp at he
  | .ite k a b t e, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ca cb ct τ1 ce τ2 ha hb ht hte
      split at he
      · rename_i heq
        subst heq
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [Ex.Pure, Bool.and_eq_true] at hp
        obtain ⟨⟨⟨pa, pb⟩, pt⟩, pe⟩ := hp
        obtain ⟨ta, ra⟩ := cE_ok hc a env vals ca .w L pa ha hr
        let x := (den (inpW c) a vals).word
        have hb' : cE env (L ++ [x]).length b = some (cb, .w) := by simpa using hb
        obtain ⟨tb, rb⟩ := cE_ok hc b env vals cb .w _ pb hb' (hr.ext _)
        obtain ⟨tt, rt⟩ := cE_ok hc t env vals ct τ1 L pt ht hr
        obtain ⟨te, re⟩ := cE_ok hc e env vals ce τ1 L pe hte hr
        simp only [den]
        refine ⟨by split <;> assumption, fun s hs hin => ?_⟩
        have ra' := ra s hs hin
        rw [ta.w] at ra'
        have hab := seq_ok (B := [(den (inpW c) b vals).word]) ra' (fun s1 hs1 k1 => by
          have rb' := rb s1 hs1 (hin.keep k1); rw [tb.w] at rb'; exact rb') hs
        have := ite_node hc hs k hab (fun _ s1 hs1 k1 => rt s1 hs1 (hin.keep k1))
          (fun _ s1 hs1 k1 => re s1 hs1 (hin.keep k1))
        rw [flat_ite]; exact this
      · simp at he
    · simp at he
  | .let_ v b, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i cv τv hv
      split at he
      · rename_i cb ρ hb
        split at he
        · rename_i hlim
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          simp only [Ex.Pure, Bool.and_eq_true] at hp
          obtain ⟨tv, rv⟩ := cE_ok hc v env vals cv τv L hp.1 hv hr
          let V := (den (inpW c) v vals).flat
          have hb' : cE ((τv, L.length) :: env) (L ++ V).length b = some (cb, ρ) := by
            simpa [V, tv.len] using hb
          obtain ⟨tb, rb⟩ := cE_ok hc b _ _ cb ρ (L ++ V) hp.2 hb' (hr.top tv rfl)
          simp only [den]
          refine ⟨tb, fun s hs hin => ?_⟩
          have := let_node hc hs (by rw [tv.len]; unfold Lim at hlim; omega)
            (by rw [tb.len]; unfold Lim at hlim; omega) (rv s hs hin)
            (fun s1 hs1 k1 => rb s1 hs1 (hin.keep k1))
          rw [tv.len, tb.len] at this
          exact this
        · simp at he
      · simp at he
    · simp at he
  | .pair a b, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ca τa ha
      split at he
      · rename_i cb τb hb
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [Ex.Pure, Bool.and_eq_true] at hp
        obtain ⟨ta, ra⟩ := cE_ok hc a env vals ca τa L hp.1 ha hr
        let A := (den (inpW c) a vals).flat
        have hb' : cE env (L ++ A).length b = some (cb, τb) := by simpa [A, ta.len] using hb
        obtain ⟨tb, rb⟩ := cE_ok hc b env vals cb τb _ hp.2 hb' (hr.ext _)
        simp only [den]
        exact ⟨⟨ta, tb⟩, fun s hs hin => seq_ok (ra s hs hin) (fun s1 hs1 k1 => rb s1 hs1 (hin.keep k1)) hs⟩
      · simp at he
    · simp at he
  | .fst e, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ce τa τb he'
      split at he
      · simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [Ex.Pure] at hp
        obtain ⟨te, re⟩ := cE_ok hc e env vals ce _ L hp he' hr
        obtain ⟨hv, t1, t2⟩ := te.prod
        simp only [den]
        refine ⟨t1, fun s hs hin => ?_⟩
        have r := re s hs hin
        rw [hv] at r
        have := drop_node hc hs r
        rw [t2.len] at this
        exact this
      · simp at he
    · simp at he
  | .snd e, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ce τa τb he'
      split at he
      · rename_i hlim
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [Ex.Pure] at hp
        obtain ⟨te, re⟩ := cE_ok hc e env vals ce _ L hp he' hr
        obtain ⟨hv, t1, t2⟩ := te.prod
        simp only [den]
        refine ⟨t2, fun s hs hin => ?_⟩
        have r := re s hs hin
        rw [hv] at r
        have := slide_node hc hs (by rw [t1.len]; unfold Lim at hlim; omega)
          (by rw [t2.len]; unfold Lim at hlim; omega) r
        rw [t1.len, t2.len] at this
        exact this
      · simp at he
    · simp at he
  | .split e b, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ce τa τb he'
      split at he
      · rename_i cb ρ hb
        split at he
        · rename_i hlim
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          simp only [Ex.Pure, Bool.and_eq_true] at hp
          obtain ⟨te, re⟩ := cE_ok hc e env vals ce _ L hp.1 he' hr
          obtain ⟨hv, t1, t2⟩ := te.prod
          let v := den (inpW c) e vals
          let A := v.fst.flat
          let B := v.snd.flat
          have l1 : A.length = τa.size := t1.len
          have l2 : B.length = τb.size := t2.len
          have hr2 : EnvRep (L ++ A ++ B) ((τb, (L ++ A).length) :: (τa, L.length) :: env) (v.snd :: v.fst :: vals) :=
            (hr.top t1 rfl).top t2 rfl
          have hb' : cE ((τb, (L ++ A).length) :: (τa, L.length) :: env) (L ++ A ++ B).length b = some (cb, ρ) := by
            rw [show (L ++ A).length = L.length + τa.size by simp [l1],
              show (L ++ A ++ B).length = L.length + τa.size + τb.size by simp [l1, l2]; omega]
            exact hb
          obtain ⟨tb, rb⟩ := cE_ok hc b _ _ cb ρ _ hp.2 hb' hr2
          simp only [den]
          refine ⟨tb, fun s hs hin => ?_⟩
          have r := re s hs hin
          rw [hv] at r
          have := let_node hc hs (V := A ++ B) (by simp [l1, l2]; unfold Lim at hlim; omega)
            (by rw [tb.len]; unfold Lim at hlim; omega) r
            (fun s1 hs1 k1 => by
              have := rb s1 (by simpa [A, B, Val.flat] using hs1) (hin.keep k1)
              simpa [A, B, Val.flat] using this)
          rw [show (A ++ B).length = τa.size + τb.size by simp [l1, l2], tb.len] at this
          exact this
        · simp at he
      · simp at he
    · simp at he
  | .mk _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp
  | .size _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp
  | .get _ _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp
  | .set _ _ _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp
  | .push _ _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp
  | .loop _ _ _ _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp

end Nano.V2B
