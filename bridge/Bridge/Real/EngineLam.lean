/- Bridge.Real.EngineLam: binders for the engine (DENOTES_GENERAL.md §2, "the λ piece").

* `wfk k e`: every free bound variable of `e` is `< k` (no `let`, `fvar`, string literal);
* `substD as d e`: substitute closed terms for the free variables at depth `≥ d`, under binders;
* `den_move`: a scoped term denotes the same under environments agreeing below its scope;
* `den_substD`: substitution commutes with denotation;
* `beta_den`: **β in either regime**: if the redex `(λ x : T. b) a` denotes `X` and `a` lies in `⟦T⟧`, then `b[a]`
  denotes `X`.  The λ's binder data is whatever the checker stored: in regime 0 the λ is `pt`, `app pt _ = pt`, and
  `Denotes.lam`'s own premise makes the body `pt` on the domain. -/
import Bridge.Real.Engine2
import Bridge.Real.Scope

namespace Bridge.Real.EngineLam
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.Real.Engine

universe w
variable {V : Type w} [SetTheory V]

section
variable {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}

/-- **substitution commutes with denotation**: the variables `≥ d` read the closed substituends' values -/
theorem den_substD {as : List Expr} :
    ∀ {e : Expr} {d : Nat} {ρ ρ' : BVarIdx → V} {Y : V}, wfk (d + as.length) e = true →
    (∀ i < d, ρ i = ρ' i) → (∀ j a, as[j]? = some a → ∀ ρ'', Denotes cval env φ ρ'' a (ρ (d + j))) →
    Denotes cval env φ ρ e Y → Denotes cval env φ ρ' (substD as d e) Y
  | .bvar j, d, ρ, ρ', _, hw, he, ha, h => by
    cases h
    simp only [wfk, decide_eq_true_eq] at hw
    by_cases hj : j < d
    · simp only [substD, hj, if_true]; rw [he j hj]; exact .bvar
    · simp only [substD, hj, if_false]
      have hl : j - d < as.length := by omega
      have hget : as[j - d]? = some (as[j - d]'hl) := List.getElem?_eq_getElem hl
      have := ha (j - d) _ hget ρ'
      rw [show d + (j - d) = j by omega] at this
      rw [List.getD_eq_getElem?_getD, hget]; exact this
  | .sort _, _, _, _, _, _, _, _, h => by cases h; exact .sort
  | .const _ _, _, _, _, _, _, _, _, h => by cases h with | const hf hl => exact .const hf hl
  | .lit (.natVal n), _, _, _, _, _, _, _, h => den_move (k := 0) rfl (fun _ h => absurd h (Nat.not_lt_zero _)) h
  | .app f a, d, ρ, ρ', _, hw, he, ha, h => by
    simp only [wfk, Bool.and_eq_true] at hw
    cases h with
    | app hf hx => exact .app (den_substD hw.1 he ha hf) (den_substD hw.2 he ha hx)
  | .lam t b m, d, ρ, ρ', _, hw, he, ha, h => by
    simp only [wfk, Bool.and_eq_true] at hw
    cases h with
    | lam hA hF hP =>
      refine .lam (den_substD hw.1 he ha hA) (fun x hx => den_substD (d := d + 1) (by
        rw [Nat.add_right_comm]; exact hw.2) ?_ ?_ (hF x hx)) hP
      · intro i hi
        cases i with
        | zero => rfl
        | succ i => exact he i (by omega)
      · intro j a hj ρ''
        rw [show d + 1 + j = (d + j) + 1 by omega]; exact ha j a hj ρ''
  | .forallE t b m, d, ρ, ρ', _, hw, he, ha, h => by
    simp only [wfk, Bool.and_eq_true] at hw
    cases h with
    | pi hA hB hP =>
      refine .pi (den_substD hw.1 he ha hA) (fun x hx => den_substD (d := d + 1) (by
        rw [Nat.add_right_comm]; exact hw.2) ?_ ?_ (hB x hx)) hP
      · intro i hi
        cases i with
        | zero => rfl
        | succ i => exact he i (by omega)
      · intro j a hj ρ''
        rw [show d + 1 + j = (d + j) + 1 by omega]; exact ha j a hj ρ''
  | .proj s i e, d, ρ, ρ', _, hw, he, ha, h => by
    simp only [wfk] at hw
    cases h with
    | proj_table ht h => exact .proj_table ht (den_substD hw he ha h)
    | proj_fst ht h => exact .proj_fst ht (den_substD hw he ha h)
    | proj_snd ht h => exact .proj_snd ht (den_substD hw he ha h)
  | .lit (.strVal _), _, _, _, _, hw, _, _, _ => by simp [wfk] at hw
  | .fvar _ _, _, _, _, _, hw, _, _, _ => by simp [wfk] at hw
  | .letE _ _ _, _, _, _, _, hw, _, _, _ => by simp [wfk] at hw

/-- **β in either regime**: a redex whose argument lies in the binder's domain denotes what the body does at the
argument's value, whatever binder data the λ carries -/
theorem beta_den {ρ : BVarIdx → V} {T b a : Expr} {m : BinderMeta} {X Xa AT : V}
    (hb : wfk 1 b = true) (ha0 : wfk 0 a = true)
    (h : Denotes cval env φ ρ (.app (.lam T b m) a) X) (hT : Denotes cval env φ ρ T AT)
    (ha : Denotes cval env φ ρ a Xa) (hm : Xa ∈ˢ AT) :
    Denotes cval env φ ρ (substD [a] 0 b) X := by
  cases h with
  | app hf hx =>
    obtain rfl := Denotes_functional ha hx
    cases hf with
    | lam hA hF hP =>
      obtain rfl := Denotes_functional hT hA
      rename_i F
      have hval : app (lamR (regime φ m.pw) AT F) Xa = F Xa := by
        by_cases hr : regime φ m.pw = 0
        · rw [hr, lamR_zero, app_pt, hP hr Xa hm]
        · rw [lamR_pos hr, app_graph hm]
      rw [hval]
      refine den_substD (as := [a]) (d := 0) (by simpa using hb) (fun _ h => absurd h (Nat.not_lt_zero _)) ?_ (hF Xa hm)
      intro j a' hj ρ''
      cases j with
      | zero =>
        simp at hj; subst hj
        exact den_move (k := 0) ha0 (fun _ h => absurd h (Nat.not_lt_zero _)) ha
      | succ j => simp at hj
/-- every binder of `e` is read in regime 1 at `φ` -/
def Reg1 (φ : LevelParam → Nat) : Expr → Prop
  | .app f a => Reg1 φ f ∧ Reg1 φ a
  | .lam t b m => Reg1 φ t ∧ Reg1 φ b ∧ regime φ m.pw ≠ 0
  | .forallE t b m => Reg1 φ t ∧ Reg1 φ b ∧ regime φ m.pw ≠ 0
  | .proj _ _ e => Reg1 φ e
  | _ => True


/-- **binder data is irrelevant once every binder is in regime 1**: such a term denotes what its
binder-data-erased form (`resetMeta`, all `.never`) denotes, and conversely -/
theorem den_reset : ∀ {e : Expr} {k : Nat} {ρ : BVarIdx → V} {Y : V}, wfk k e = true → Reg1 φ e →
    (Denotes cval env φ ρ e Y ↔ Denotes cval env φ ρ e.resetMeta Y)
  | .bvar _, _, _, _, _, _ => by simp [Expr.resetMeta]
  | .sort _, _, _, _, _, _ => by simp [Expr.resetMeta]
  | .const _ _, _, _, _, _, _ => by simp [Expr.resetMeta]
  | .lit _, _, _, _, _, _ => by simp [Expr.resetMeta]
  | .app f a, k, ρ, Y, hw, hr => by
    simp only [wfk, Bool.and_eq_true] at hw
    simp only [Expr.resetMeta]
    constructor
    · intro h; cases h with
      | app hf ha => exact .app ((den_reset hw.1 hr.1).mp hf) ((den_reset hw.2 hr.2).mp ha)
    · intro h; cases h with
      | app hf ha => exact .app ((den_reset hw.1 hr.1).mpr hf) ((den_reset hw.2 hr.2).mpr ha)
  | .lam t b m, k, ρ, Y, hw, hr => by
    simp only [wfk, Bool.and_eq_true] at hw
    simp only [Expr.resetMeta]
    obtain ⟨h1, h2, h3⟩ := hr
    constructor
    · intro h; cases h with
      | lam hA hF hP =>
        rw [lamR_pos h3, ← lamR_pos (v := regime φ (⟨.never⟩ : BinderMeta).pw) (by rw [regime_never]; exact Nat.one_ne_zero)]
        exact .lam ((den_reset hw.1 h1).mp hA) (fun x hx => (den_reset hw.2 h2).mp (hF x hx))
          (fun h0 => by rw [regime_never] at h0; exact absurd h0 Nat.one_ne_zero)
    · intro h; cases h with
      | lam hA hF hP =>
        rw [lamR_pos (by rw [regime_never]; exact Nat.one_ne_zero), ← lamR_pos h3]
        exact .lam ((den_reset hw.1 h1).mpr hA) (fun x hx => (den_reset hw.2 h2).mpr (hF x hx))
          (fun h0 => absurd h0 h3)
  | .forallE t b m, k, ρ, Y, hw, hr => by
    simp only [wfk, Bool.and_eq_true] at hw
    simp only [Expr.resetMeta]
    obtain ⟨h1, h2, h3⟩ := hr
    constructor
    · intro h; cases h with
      | pi hA hB hP =>
        rw [piR_pos h3, ← piR_pos (v := regime φ (⟨.never⟩ : BinderMeta).pw) (by rw [regime_never]; exact Nat.one_ne_zero)]
        exact .pi ((den_reset hw.1 h1).mp hA) (fun x hx => (den_reset hw.2 h2).mp (hB x hx))
          (fun h0 => by rw [regime_never] at h0; exact absurd h0 Nat.one_ne_zero)
    · intro h; cases h with
      | pi hA hB hP =>
        rw [piR_pos (by rw [regime_never]; exact Nat.one_ne_zero), ← piR_pos h3]
        exact .pi ((den_reset hw.1 h1).mpr hA) (fun x hx => (den_reset hw.2 h2).mpr (hB x hx))
          (fun h0 => absurd h0 h3)
  | .proj s i e, k, ρ, Y, hw, hr => by
    simp only [wfk] at hw
    simp only [Expr.resetMeta]
    constructor
    · intro h; cases h with
      | proj_table ht h => exact .proj_table ht ((den_reset hw hr).mp h)
      | proj_fst ht h => exact .proj_fst ht ((den_reset hw hr).mp h)
      | proj_snd ht h => exact .proj_snd ht ((den_reset hw hr).mp h)
    · intro h; cases h with
      | proj_table ht h => exact .proj_table ht ((den_reset hw hr).mpr h)
      | proj_fst ht h => exact .proj_fst ht ((den_reset hw hr).mpr h)
      | proj_snd ht h => exact .proj_snd ht ((den_reset hw hr).mpr h)
  | .fvar _ _, _, _, _, hw, _ => by simp [wfk] at hw
  | .letE _ _ _, _, _, _, hw, _ => by simp [wfk] at hw
end

end Bridge.Real.EngineLam
