/- Bridge.ModelExists2 — DRAFT, NOT BUILT (the con-leche build was denied by the session's permission classifier on
2026-11-23 ~11:15; not in any lakefile root).

`model_exists'`: `model_exists` plus `cval_params`, the field FABLE-MINI proposed (Universe.lean / UNIVERSE_NOTE.md)
to settle finding (a). It needs no upstream change. The proof follows `MainTheorem.model_exists`
(MainTheorem.lean:96): the model is `Model.ofEnvModelM m` (Model/Denotes.lean:379), whose
`cval := cvalOf m.base2.acval`; `cvalOf acval n ψ = interp V (fun _ => ∅) (acval n ψ)` (Model/Denotes.lean:57). So
`cval_params` is `congrArg` of the core carrier's own `EnvModel.acval_params` (Model/Annot/EnvModel.lean:60).

Risk to check when building: `Model.ofEnvModelM` lives in a `Model/*` module, whose defs are not `@[expose]`d
(CLAUDE.md, "The module system"). If `(Model.ofEnvModelM m).cval` does not unfold here, then either (i) add a
one-line exposed lemma `ofEnvModelM_cval` upstream (owner decision), or (ii) build the `Model` in the bridge itself
by copying `ofEnvModelM`'s three fields (mem / eq_equality / false_empty, ~60 lines that call only public lemmas). -/
import ConLeche

namespace Bridge.ModelExists2
open ConLeche SetTheory

universe w

/-- a model's constant valuation reads only the constant's own level parameters -/
def CvalParams {V : Type w} [SetTheory V] {env : Env} (M : Model V env) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) → M.cval n ψ₁ = M.cval n ψ₂

theorem model_exists' (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (accepted : Cached.checkDecls .verified pins ds = .ok env) :
    ∃ M : Model V env, CvalParams M := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  refine ⟨Model.Model.ofEnvModelM m, fun n ci hf ψ₁ ψ₂ hp => ?_⟩
  show Model.cvalOf m.base2.acval n ψ₁ = Model.cvalOf m.base2.acval n ψ₂
  unfold Model.cvalOf
  rw [m.base2.acval_params n ci hf ψ₁ ψ₂ hp]

end Bridge.ModelExists2
