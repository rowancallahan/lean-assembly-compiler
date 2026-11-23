/- Bridge.Real.TySubst: typing is stable under substitution of typed closed values (DENOTES_GENERAL §5 (1)).

`hasTy_subst`: if `e : T` in context `Δ ++ Ts` (all context types closed), and `vs` are values with `vs[j] : Ts[j]`
in every context, then `substD vs |Δ| e : substD vs |Δ| T` in context `Δ`.  This is what lets the general invariant
carry typing of an emitted term through the environment's values (the `let`/β case needs the body typed under
its binder). -/
import Bridge.Real.EngineLam

namespace Bridge.Real.TySubst
open ConLeche Bridge Bridge.Real Bridge.Real.Engine Bridge.Real.EngineLam

theorem sc_inst {ps : List Name} {us : List Level} : ∀ {k : Nat} {e : Expr}, sc k e = true → sc k (inst ps us e) = true
  | _, .bvar _, h => by simpa [inst, Expr.instantiateLevelParams] using h
  | _, .sort _, _ => by simp [inst, Expr.instantiateLevelParams, sc]
  | _, .const _ _, _ => by simp [inst, Expr.instantiateLevelParams, sc]
  | _, .lit (.natVal _), _ => by simp [inst, Expr.instantiateLevelParams, sc]
  | _, .app f a, h => by
    simp only [sc, Bool.and_eq_true] at h
    have h1 := sc_inst (ps := ps) (us := us) h.1
    have h2 := sc_inst (ps := ps) (us := us) h.2
    simp only [inst] at h1 h2 ⊢
    simp only [Expr.instantiateLevelParams, sc, Bool.and_eq_true]
    exact ⟨h1, h2⟩
  | _, .lit (.strVal _), h | _, .fvar _ _, h | _, .lam _ _ _, h | _, .forallE _ _ _, h
  | _, .letE _ _ _, h | _, .proj _ _ _, h => by simp [sc] at h

theorem sc_wfk : ∀ {k : Nat} {e : Expr}, sc k e = true → wfk k e = true
  | _, .bvar _, h => by simpa [sc, wfk] using h
  | _, .sort _, _ | _, .const _ _, _ | _, .lit (.natVal _), _ => rfl
  | _, .app f a, h => by
    simp only [sc, Bool.and_eq_true] at h
    simp only [wfk, Bool.and_eq_true]; exact ⟨sc_wfk h.1, sc_wfk h.2⟩
  | _, .lit (.strVal _), h | _, .fvar _ _, h | _, .lam _ _ _, h | _, .forallE _ _ _, h
  | _, .letE _ _ _, h | _, .proj _ _ _, h => by simp [sc] at h

/-- a term scoped below `k` is untouched by substitution at depth `≥ k` -/
theorem substD_closed {vs : List Expr} : ∀ {k : Nat} {e : Expr}, wfk k e = true → ∀ {d : Nat}, k ≤ d → substD vs d e = e
  | _, .bvar j, h, d, hd => by
    simp only [wfk, decide_eq_true_eq] at h
    simp [substD, show j < d by omega]
  | _, .sort _, _, _, _ | _, .const _ _, _, _, _ | _, .lit (.natVal _), _, _, _ => rfl
  | _, .app f a, h, d, hd => by
    simp only [wfk, Bool.and_eq_true] at h
    simp only [substD, substD_closed h.1 hd, substD_closed h.2 hd]
  | _, .lam t b m, h, d, hd => by
    simp only [wfk, Bool.and_eq_true] at h
    simp only [substD, substD_closed h.1 hd, substD_closed h.2 (Nat.succ_le_succ hd)]
  | _, .forallE t b m, h, d, hd => by
    simp only [wfk, Bool.and_eq_true] at h
    simp only [substD, substD_closed h.1 hd, substD_closed h.2 (Nat.succ_le_succ hd)]
  | _, .proj s i e, h, d, hd => by
    simp only [wfk] at h
    simp only [substD, substD_closed h hd]
  | _, .lit (.strVal _), h, _, _ | _, .fvar _ _, h, _, _ | _, .letE _ _ _, h, _, _ => by simp [wfk] at h

/-- substitution commutes with a binder-free argument substitution -/
theorem substD_substB {vs : List Expr} {d : Nat} :
    ∀ {n : Nat} {as : List Expr} {X : Expr}, sc n X = true → n ≤ as.length →
      substD vs d (substB as X) = substB (as.map (substD vs d)) X
  | _, as, .bvar j, h, hn => by
    simp only [sc, decide_eq_true_eq] at h
    have hj : j < as.length := by omega
    simp [substB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  | _, _, .sort _, _, _ | _, _, .const _ _, _, _ | _, _, .lit (.natVal _), _, _ => by simp [substB, substD]
  | _, _, .app f a, h, hn => by
    simp only [sc, Bool.and_eq_true] at h
    simp only [substB, substD, substD_substB h.1 hn, substD_substB h.2 hn]
  | _, _, .lit (.strVal _), h, _ | _, _, .fvar _ _, h, _ | _, _, .lam _ _ _, h, _ | _, _, .forallE _ _ _, h, _
  | _, _, .letE _ _ _, h, _ | _, _, .proj _ _ _, h, _ => by simp [sc] at h

theorem substD_apps {vs : List Expr} {d : Nat} :
    ∀ {f : Expr} {as : List Expr}, substD vs d (apps f as) = apps (substD vs d f) (as.map (substD vs d))
  | _, [] => rfl
  | f, a :: as => by simp only [apps, List.map_cons]; rw [substD_apps]; rfl

section
variable {tab : Tab} {eqs : List (Expr × Expr)}
  (heqs : ∀ p ∈ eqs, sc 0 p.1 = true ∧ sc 0 p.2 = true)
  (htab : ∀ n h, tab n = some h → Engine.headSc h = true)
  {vs Ts : List Expr} (hlen : vs.length = Ts.length)
  (hv : ∀ (j : Nat) (v T : Expr), vs[j]? = some v → Ts[j]? = some T → ∀ Δ, HasTy tab eqs Δ v T)
  (hTs : ∀ T ∈ Ts, wfk 0 T = true)
include heqs htab hlen hv hTs

mutual
/-- **typing under substitution** -/
theorem hasTy_subst : ∀ {Γ : List Expr} {e T : Expr}, HasTy tab eqs Γ e T →
    ∀ (Δ : List Expr), Γ = Δ ++ Ts → (∀ U ∈ Δ, wfk 0 U = true) →
    HasTy tab eqs Δ (substD vs Δ.length e) (substD vs Δ.length T)
  | _, _, _, .sort, Δ, _, _ => by simp only [substD]; exact .sort
  | _, _, _, .conv h hp, Δ, hΓ, hΔ => by
    have ih := hasTy_subst h Δ hΓ hΔ
    have h1 := substD_closed (vs := vs) (sc_wfk (heqs _ hp).1) (Nat.zero_le Δ.length)
    have h2 := substD_closed (vs := vs) (sc_wfk (heqs _ hp).2) (Nat.zero_le Δ.length)
    simp only at h1 h2
    rw [h1] at ih; rw [h2]; exact .conv ih hp
  | _, _, _, .bvar (i := i) (T := T) hi, Δ, hΓ, hΔ => by
    subst hΓ
    by_cases hd : i < Δ.length
    · rw [List.getElem?_append_left hd] at hi
      have hT := hΔ T (List.mem_of_getElem? hi)
      rw [substD_closed hT (Nat.zero_le _)]
      simp only [substD, hd, ite_true]; exact .bvar hi
    · rw [List.getElem?_append_right (by omega)] at hi
      have hT := hTs T (List.mem_of_getElem? hi)
      rw [substD_closed hT (Nat.zero_le _)]
      have hl : i - Δ.length < vs.length := by
        rw [hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
      have hget : vs[i - Δ.length]? = some (vs[i - Δ.length]'hl) := List.getElem?_eq_getElem hl
      simp only [substD, hd, if_false, List.getD_eq_getElem?_getD, hget, Option.getD_some]
      exact hv _ _ _ hget hi Δ
  | _, _, _, .lit, Δ, _, _ => by simp only [substD]; exact .lit
  | _, _, _, .head (n := n) (us := us) (h := h) (as := as) htn hus hargs, Δ, hΓ, hΔ => by
    have hsc := htab n h htn
    simp only [Engine.headSc, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hsc
    rw [substD_apps]
    simp only [substD]
    rw [substD_substB (n := as.reverse.length) (by rw [List.length_reverse, hargs.length]; exact sc_inst hsc.2) (Nat.le_refl _),
      List.map_reverse]
    refine .head htn hus ?_
    have := argsTy_subst hargs Δ hΓ hΔ (fun i T hi => by
      have hl : i < h.Ts.length := (List.getElem?_eq_some_iff.mp hi).1
      have := hsc.1 i hl
      simp only [List.getD_eq_getElem?_getD, hi, Option.getD_some] at this
      simpa using this)
    simpa using this
  | _, _, _, .lam (T := T) (b := b) (S := S) hTy hT hS hG hb, Δ, hΓ, hΔ => by
    have ih1 := hasTy_subst hTy Δ hΓ hΔ
    have ih2 := hasTy_subst hb (T :: Δ) (by rw [hΓ]; rfl) (by
      intro U hU; simp only [List.mem_cons] at hU; rcases hU with rfl | hU
      · exact hT
      · exact hΔ U hU)
    rw [substD_closed hT (Nat.zero_le _)] at ih1
    simp only [List.length_cons] at ih2
    rw [substD_closed hS (Nat.zero_le _)] at ih2
    simp only [substD, substD_closed hT (Nat.zero_le _), substD_closed hS (Nat.zero_le _)] at ih1 ⊢
    exact .lam ih1 hT hS hΔ ih2
  | _, _, _, .app (S := S) hf ha hS, Δ, hΓ, hΔ => by
    have ih1 := hasTy_subst hf Δ hΓ hΔ
    have ih2 := hasTy_subst ha Δ hΓ hΔ
    simp only [substD, substD_closed hS (Nat.zero_le _)] at ih1 ⊢
    exact .app ih1 ih2 hS
theorem argsTy_subst : ∀ {Γ : List Expr} {ps : List Name} {us : List Level} {Ts' as done : List Expr},
    ArgsTy tab eqs Γ ps us Ts' as done →
    ∀ (Δ : List Expr), Γ = Δ ++ Ts → (∀ U ∈ Δ, wfk 0 U = true) →
    (∀ i T, Ts'[i]? = some T → sc (done.length + i) T = true) →
    ArgsTy tab eqs Δ ps us Ts' (as.map (substD vs Δ.length)) (done.map (substD vs Δ.length))
  | _, _, _, _, _, _, .nil, _, _, _, _ => .nil
  | _, ps, us, T :: Ts', a :: as, done, .cons ha hr, Δ, hΓ, hΔ, hsc => by
    have ih := hasTy_subst ha Δ hΓ hΔ
    rw [substD_substB (n := done.length) (sc_inst (by simpa using hsc 0 T rfl)) (Nat.le_refl _)] at ih
    have ih2 := argsTy_subst hr Δ hΓ hΔ (fun i T' hi => by
      have := hsc (i + 1) T' (by simpa using hi); simpa [Nat.add_assoc, Nat.add_comm 1] using this)
    exact .cons ih ih2
end
end

end Bridge.Real.TySubst
