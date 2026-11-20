/- Simulation between IR programs (`Testing/notes/IR_DESIGN.md` §2.4): a forward simulation (one source step to
zero or more target steps, related results) gives refinement of terminating runs; refinements compose.

Both sides are deterministic (`run_det`) and only terminating runs are claimed (as `Computes`), so forward
simulation is enough and no measure is needed: a source step always uses one unit of fuel.

Pure Lean (core only). -/
import Legacy.Compiler.Ir.Sem

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

section
variable {ρ σ τ : Type} [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ]

/-- `n` steps, all ordinary -/
def steps (P : Prog ρ) : Nat → State ρ → Option (State ρ)
  | 0, s => some s
  | n + 1, s => match step P s with
    | .next s' => steps P n s'
    | _ => none

theorem run_steps {P : Prog ρ} : ∀ {k m : Nat} {t t' : State ρ} {r : Result}, steps P k t = some t' →
    run P m t' = some r → run P (k + m) t = some r
  | 0, m, t, t', r, h, h' => by
    simp only [steps, Option.some.injEq] at h; subst h; simpa using h'
  | k + 1, m, t, t', r, h, h' => by
    simp only [steps] at h
    split at h
    · next t₁ e =>
      rw [show k + 1 + m = (k + m) + 1 by omega, run_succ, e]
      exact run_steps h h'
    · exact nomatch h

/-- **forward simulation** of `P` by `Q` -/
structure Sim (P : Prog ρ) (Q : Prog σ) where
  R : State ρ → State σ → Prop
  RR : Result → Result → Prop
  next : ∀ {s t s'}, R s t → step P s = .next s' → ∃ k t', steps Q k t = some t' ∧ R s' t'
  done : ∀ {s t r}, R s t → step P s = .done r →
    ∃ k t' r', steps Q k t = some t' ∧ step Q t' = .done r' ∧ RR r r'

/-- refinement of terminating runs -/
def Refines (P : Prog ρ) (s : State ρ) (Q : Prog σ) (t : State σ) (RR : Result → Result → Prop) : Prop :=
  ∀ r, Runs P s r → ∃ r', Runs Q t r' ∧ RR r r'

theorem Sim.run_ok {P : Prog ρ} {Q : Prog σ} (S : Sim P Q) : ∀ {n : Nat} {s : State ρ} {t : State σ} {r : Result},
    S.R s t → run P n s = some r → ∃ r', Runs Q t r' ∧ S.RR r r'
  | 0, _, _, _, _, h => nomatch h
  | n + 1, s, t, r, hR, h => by
    rw [run_succ] at h
    split at h
    · next s' e =>
      obtain ⟨k, t', hk, hR'⟩ := S.next hR e
      obtain ⟨r', ⟨m, hm⟩, hrr⟩ := S.run_ok hR' h
      exact ⟨r', ⟨k + m, run_steps hk hm⟩, hrr⟩
    · next r₀ e =>
      cases h
      obtain ⟨k, t', r', hk, hd, hrr⟩ := S.done hR e
      refine ⟨r', ⟨k + 1, run_steps hk (by rw [run_succ, hd])⟩, hrr⟩
    · exact nomatch h

/-- **simulation gives refinement** -/
theorem Sim.refines {P : Prog ρ} {Q : Prog σ} (S : Sim P Q) {s : State ρ} {t : State σ} (h : S.R s t) :
    Refines P s Q t S.RR :=
  fun _ ⟨_, hr⟩ => S.run_ok h hr

/-- **composition** -/
theorem Refines.trans {P : Prog ρ} {Q : Prog σ} {U : Prog τ} {s : State ρ} {t : State σ} {u : State τ}
    {R₁ R₂ : Result → Result → Prop} (h₁ : Refines P s Q t R₁) (h₂ : Refines Q t U u R₂) :
    Refines P s U u fun a c => ∃ b, R₁ a b ∧ R₂ b c :=
  fun r hr =>
    let ⟨r₁, h1, e1⟩ := h₁ r hr
    let ⟨r₂, h2, e2⟩ := h₂ r₁ h1
    ⟨r₂, h2, r₁, e1, e2⟩

theorem Refines.mono {P : Prog ρ} {Q : Prog σ} {s : State ρ} {t : State σ} {R₁ R₂ : Result → Result → Prop}
    (h : Refines P s Q t R₁) (hR : ∀ a b, R₁ a b → R₂ a b) : Refines P s Q t R₂ :=
  fun r hr => let ⟨r', h', e⟩ := h r hr; ⟨r', h', hR _ _ e⟩

theorem Refines.refl (P : Prog ρ) (s : State ρ) : Refines P s P s Eq := fun r hr => ⟨r, hr, rfl⟩

/-- a whole-program refinement: from every input's start -/
def ProgRefines (P : Prog ρ) (Q : Prog σ) (RR : Result → Result → Prop) : Prop :=
  ∀ input, Refines P (init P input) Q (init Q input) RR

theorem ProgRefines.trans {P : Prog ρ} {Q : Prog σ} {U : Prog τ} {R₁ R₂ : Result → Result → Prop}
    (h₁ : ProgRefines P Q R₁) (h₂ : ProgRefines Q U R₂) : ProgRefines P U fun a c => ∃ b, R₁ a b ∧ R₂ b c :=
  fun input => (h₁ input).trans (h₂ input)

end
end Proven.Ir
