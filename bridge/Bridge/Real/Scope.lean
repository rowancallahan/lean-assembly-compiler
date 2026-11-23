/- Bridge.Real.Scope: scope (`wfk`), substitution under binders (`substD`), and moving a scoped term's
denotation between environments that agree below its scope (`den_move`).  Used by the engine's binder rules. -/
import ConLeche.MainTheorem
import Bridge.ModelExists2
import Bridge.Real.Tiny

namespace Bridge.Real.EngineLam
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real

universe w
variable {V : Type w} [SetTheory V]

/-- scope: every free bound variable is `< k` -/
def wfk : Nat → Expr → Bool
  | k, .bvar j => j < k
  | k, .app f a => wfk k f && wfk k a
  | k, .lam t b _ => wfk k t && wfk (k + 1) b
  | k, .forallE t b _ => wfk k t && wfk (k + 1) b
  | k, .proj _ _ e => wfk k e
  | _, .sort _ | _, .const _ _ | _, .lit (.natVal _) => true
  | _, _ => false

theorem regime_never (φ : LevelParam → Nat) : regime φ (⟨.never⟩ : BinderMeta).pw = 1 := by
  simp [regime]

/-- substitute closed terms for the free variables at depth `≥ d`, under binders -/
def substD (as : List Expr) (d : Nat) : Expr → Expr
  | .bvar j => if j < d then .bvar j else as.getD (j - d) (.bvar 0)
  | .app f a => .app (substD as d f) (substD as d a)
  | .lam t b m => .lam (substD as d t) (substD as (d + 1) b) m
  | .forallE t b m => .forallE (substD as d t) (substD as (d + 1) b) m
  | .proj s i e => .proj s i (substD as d e)
  | e => e

section
variable {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}

/-- a scoped term denotes the same under environments that agree below its scope -/
theorem den_move : ∀ {e : Expr} {k : Nat} {ρ ρ' : BVarIdx → V} {Y : V}, wfk k e = true →
    (∀ i < k, ρ i = ρ' i) → Denotes cval env φ ρ e Y → Denotes cval env φ ρ' e Y
  | .bvar j, k, ρ, ρ', _, hw, he, h => by
    cases h; simp only [wfk, decide_eq_true_eq] at hw; rw [he j hw]; exact .bvar
  | .sort _, _, _, _, _, _, _, h => by cases h; exact .sort
  | .const _ _, _, _, _, _, _, _, h => by cases h with | const hf hl => exact .const hf hl
  | .lit (.natVal n), _, _, _, _, _, _, h => by
    cases h with
    | natLit h =>
      refine .natLit ?_
      cases n with
      | zero => cases h with | const hf hl => exact .const hf hl
      | succ n =>
        cases h with
        | app hf ha =>
          cases hf with
          | const hf hl => exact .app (.const hf hl) (den_move (k := 0) rfl (fun _ h => absurd h (Nat.not_lt_zero _)) ha)
  | .app f a, k, ρ, ρ', _, hw, he, h => by
    simp only [wfk, Bool.and_eq_true] at hw
    cases h with
    | app hf ha => exact .app (den_move hw.1 he hf) (den_move hw.2 he ha)
  | .lam t b m, k, ρ, ρ', _, hw, he, h => by
    simp only [wfk, Bool.and_eq_true] at hw
    cases h with
    | lam hA hF hP =>
      refine .lam (den_move hw.1 he hA) (fun x hx => den_move hw.2 ?_ (hF x hx)) hP
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact he i (by omega)
  | .forallE t b m, k, ρ, ρ', _, hw, he, h => by
    simp only [wfk, Bool.and_eq_true] at hw
    cases h with
    | pi hA hB hP =>
      refine .pi (den_move hw.1 he hA) (fun x hx => den_move hw.2 ?_ (hB x hx)) hP
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact he i (by omega)
  | .proj s i e, k, ρ, ρ', _, hw, he, h => by
    simp only [wfk] at hw
    cases h with
    | proj_table ht h => exact .proj_table ht (den_move hw he h)
    | proj_fst ht h => exact .proj_fst ht (den_move hw he h)
    | proj_snd ht h => exact .proj_snd ht (den_move hw he h)
  | .lit (.strVal _), _, _, _, _, hw, _, _ => by simp [wfk] at hw
  | .fvar _ _, _, _, _, _, hw, _, _ => by simp [wfk] at hw
  | .letE _ _ _, _, _, _, _, hw, _, _ => by simp [wfk] at hw

end

end Bridge.Real.EngineLam
