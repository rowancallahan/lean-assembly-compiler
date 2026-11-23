/-
Universe.lean — the universe-level issue in con-leche's `Model` (dwijayuda/con-leche @ 3b37939).
Standalone, no imports.  See UNIVERSE_NOTE.md for the summary.

Copied (verbatim modulo computed fields / `Lean.Name`):
* `Level`          ConLeche/Kernel/Expr.lean:39
* `Level.eval`     ConLeche/Verify/Level.lean:26
* `Level.substFn`  ConLeche/Verify/Level.lean:34
* `Denotes`        ConLeche/Denotes.lean:133, rules bvar(137) sort(140) const(144) app(151) only
* `Model`          ConLeche/Denotes.lean:265, field `mem` only (`false_empty`/`eq_equality` are
                   vacuous in the countermodel env below: neither `False` nor `Eq` is stored)
Trimmed: `SetTheory` to `mem`/`univ`/`app`; `ConstantInfo` to name/levelParams/type;
`Env.find?` is a list lookup.
-/
namespace Universe
open Lean (Name)
universe w

inductive Level | zero | succ (u : Level) | max (u v : Level) | imax (u v : Level) | param (n : Name)

namespace Level
def eval (φ : Name → Nat) : Level → Nat
  | .zero => 0
  | .succ l => eval φ l + 1
  | .max l r => Max.max (eval φ l) (eval φ r)
  | .imax l r => if eval φ r = 0 then 0 else Max.max (eval φ l) (eval φ r)
  | .param n => φ n

def substFn (φ : Name → Nat) : List Name → List Level → Name → Nat
  | k :: ks, v :: vs, n => if k = n then eval φ v else substFn φ ks vs n
  | _, _, n => φ n

/-- (a) ROOT CAUSE.  A level-parameter-free constant used at `[]` is read at the AMBIENT
assignment: `Denotes.const` gives `cval n (substFn φ [] [])`, and that is `cval n φ`. -/
theorem substFn_nil (φ : Name → Nat) : substFn φ [] [] = φ := by funext n; simp [substFn]

/-- (b1) WORKAROUND needing no Model change: an instantiation whose levels evaluate, at `φ`,
to what `φ` already assigns the parameters does not move the assignment. -/
theorem substFn_fixed (φ : Name → Nat) : ∀ (ps : List Name) (us : List Level),
    (∀ pu ∈ ps.zip us, eval φ pu.2 = φ pu.1) → substFn φ ps us = φ
  | [], _, _ => by funext n; simp [substFn]
  | _ :: _, [], _ => by funext n; simp [substFn]
  | p :: ps, u :: us, h => by
    funext n
    simp only [substFn]
    split
    · next hk => subst hk; exact h (p, u) (by simp)
    · rw [substFn_fixed φ ps us (fun pu hpu => h pu (by simp [hpu]))]

/-- At the all-ones assignment, every instantiation at levels of value 1 (`ite.{1}`,
`Nat.casesOn.{1}`, `Eq.{1}`, …) stays at the all-ones assignment. -/
theorem substFn_ones (ps : List Name) (us : List Level)
    (h : ∀ u ∈ us, eval (fun _ => 1) u = 1) :
    substFn (fun _ => 1) ps us = fun _ => 1 :=
  substFn_fixed _ _ _ (fun _ hpu => h _ (List.of_mem_zip hpu).2)

/-- Aligned instantiations at levels with equal values agree on the constant's own params. -/
theorem substFn_agree {φ ψ : Name → Nat} : ∀ (ps : List Name) (us : List Level),
    us.length = ps.length → (∀ u ∈ us, eval φ u = eval ψ u) →
    ∀ p ∈ ps, substFn φ ps us p = substFn ψ ps us p
  | [], _, _, _, _, hp => nomatch hp
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | k :: ks, u :: us, hl, h, p, hp => by
    by_cases hk : k = p
    · simp only [substFn, hk, ite_true]; exact h u (by simp)
    · simp only [substFn, hk, ite_false]
      refine substFn_agree ks us (by simpa using hl) (fun u hu => h u (by simp [hu])) p ?_
      cases hp with
      | head => exact absurd rfl hk
      | tail _ h => exact h
end Level

class SetTheory (V : Type w) where
  mem : V → V → Prop
  univ : Nat → V
  app : V → V → V
open SetTheory

inductive Expr
  | bvar (i : Nat)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : Expr)

structure ConstantInfo where
  name : Name
  levelParams : List Name
  type : Expr

structure Env where consts : List ConstantInfo
def Env.find? (env : Env) (n : Name) : Option ConstantInfo := env.consts.find? (·.name == n)

variable {V : Type w} [SetTheory V]

inductive Denotes (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat) :
    (Nat → V) → Expr → V → Prop
  | bvar {ρ : Nat → V} {i : Nat} : Denotes cval env φ ρ (.bvar i) (ρ i)
  | sort {ρ : Nat → V} {u : Level} : Denotes cval env φ ρ (.sort u) (univ (Level.eval φ u))
  | const {ρ : Nat → V} {n : Name} {us : List Level} {ci : ConstantInfo}
      (hf : env.find? n = some ci) (hlen : us.length = ci.levelParams.length) :
      Denotes cval env φ ρ (.const n us) (cval n (Level.substFn φ ci.levelParams us))
  | app {ρ : Nat → V} {f a : Expr} {F X : V}
      (hf : Denotes cval env φ ρ f F) (ha : Denotes cval env φ ρ a X) :
      Denotes cval env φ ρ (.app f a) (app F X)

structure Model (V : Type w) [SetTheory V] (env : Env) where
  cval : Name → (Name → Nat) → V
  mem : ∀ c ∈ env.consts, ∀ (φ : Name → Nat) (ρ : Nat → V),
    ∃ T, Denotes cval env φ ρ c.type T ∧ SetTheory.mem (cval c.name φ) T

/-! ## (b2) Independence of φ is NOT provable from `Model`: a countermodel -/

def c0 : ConstantInfo := ⟨`c, [], .sort (.succ .zero)⟩   -- axiom c : Type, no level params
def env0 : Env := ⟨[c0]⟩

/-- Two members of `univ 1`, selected by the assignment at a name no constant binds. -/
def glue (A B : V) : Name → (Name → Nat) → V := fun _ φ => if φ `z = 0 then A else B

def counterModel {A B : V} (hA : mem A (univ 1)) (hB : mem B (univ 1)) : Model V env0 where
  cval := glue A B
  mem := by
    intro c hc φ ρ
    simp only [env0, List.mem_singleton] at hc
    subst hc
    refine ⟨univ (Level.eval φ (.succ .zero)), .sort, ?_⟩
    show mem (if φ `z = 0 then A else B) (univ 1)
    split <;> assumption

theorem find_c0 : env0.find? `c = some c0 := by simp [env0, Env.find?, c0]

/-- **Impossibility.**  Whenever `univ 1` has two distinct members, some `Model` makes the
closed, level-parameter-free term `c` denote different sets under different assignments. -/
theorem levelFree_not_invariant {A B : V} (hA : mem A (univ 1)) (hB : mem B (univ 1))
    (hne : A ≠ B) (ρ : Nat → V) :
    ∃ (m : Model V env0) (φ ψ : Name → Nat) (X Y : V),
      Denotes m.cval env0 φ ρ (.const `c []) X ∧ Denotes m.cval env0 ψ ρ (.const `c []) Y ∧
      X ≠ Y := by
  refine ⟨counterModel hA hB, fun _ => 0, fun _ => 1, A, B, ?_, ?_, hne⟩
  · have h := Denotes.const (cval := glue A B) (φ := fun _ => 0) (ρ := ρ) (us := []) find_c0 rfl
    simp [glue, Level.substFn, c0] at h
    exact h
  · have h := Denotes.const (cval := glue A B) (φ := fun _ => 1) (ρ := ρ) (us := []) find_c0 rfl
    simp [glue, Level.substFn, c0] at h
    exact h

/-! ## (c) The field to propose, and the shift lemma it buys -/

/-- PROPOSED `Model` FIELD (`cval_params`): a constant's value reads only its own level
parameters.  It is con-leche's internal `EnvModel.acval_params`
(= `AcvalParamsAt`, ConLeche/Model/Levels.lean:53) restated for the public `cval`. -/
def CvalParams (cval : Name → (Name → Nat) → V) (env : Env) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.levelParams, ψ₁ p = ψ₂ p) → cval n ψ₁ = cval n ψ₂

/-- Every level occurring in `e` has the same value at `φ` and `ψ` (true of any term whose
levels are closed). -/
def Agree (φ ψ : Name → Nat) : Expr → Prop
  | .bvar _ => True
  | .sort u => Level.eval φ u = Level.eval ψ u
  | .const _ us => ∀ u ∈ us, Level.eval φ u = Level.eval ψ u
  | .app f a => Agree φ ψ f ∧ Agree φ ψ a

/-- **Shift lemma.**  Under `CvalParams`, a term's denotation does not depend on the
assignment beyond the values of its own levels. -/
theorem Denotes.shift {cval : Name → (Name → Nat) → V} {env : Env} {φ ψ : Name → Nat}
    (hext : CvalParams cval env) {ρ : Nat → V} {e : Expr} {v : V}
    (h : Denotes cval env φ ρ e v) : Agree φ ψ e → Denotes cval env ψ ρ e v := by
  induction h with
  | bvar => intro _; exact .bvar
  | sort => intro ha; simp only [Agree] at ha; rw [ha]; exact .sort
  | const hf hlen =>
    intro ha
    rw [hext _ _ hf _ _ (Level.substFn_agree _ _ hlen ha)]
    exact .const hf hlen
  | app _ _ ihf iha => intro ha; exact .app (ihf ha.1) (iha ha.2)

omit [SetTheory V] in
/-- Level-parameter-free constants are φ-independent under the proposed field. -/
theorem cval_levelFree {cval : Name → (Name → Nat) → V} {env : Env} (hext : CvalParams cval env)
    {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci) (h0 : ci.levelParams = [])
    (φ ψ : Name → Nat) : cval n φ = cval n ψ :=
  hext n ci hf φ ψ (by rw [h0]; intro p hp; exact nomatch hp)

end Universe

#print axioms Universe.Level.substFn_ones
#print axioms Universe.levelFree_not_invariant
#print axioms Universe.Denotes.shift
