/- The limits of Lean's own elaborator as a stated domain predicate (owner's request, NANO.md "RESOURCE LIMITS":
Lean fails on ≥ 512 nested `let`s, ≥ 256 nested calls, chains of ≥ ~3000 operands): `LeanLimits src` bounds the
elaborated program's nesting by 400 and its left operator chains by 2500. Shared by the compositions. -/
import Nano.SelfHost
import Nano.Proof

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano

/-- nesting of an expression: `let` bodies, call arguments (cost 2), right operands (parenthesized) -/
def nest : Ex → Nat
  | .num _ => 0
  | .var _ => 0
  | .add a b => max (nest a) (nest b + 1)
  | .sub a b => max (nest a) (nest b + 1)
  | .mul a b => max (nest a) (nest b + 1)
  | .let_ v b => max (nest v + 1) (nest b + 1)
  | .call b as => max (nest b) (nest as + 2)
  | .anil => 0
  | .acons e r => max (nest e) (nest r)

/-- the longest chain of left-nested binary operators -/
def chain : Ex → Nat
  | .num _ => 0
  | .var _ => 0
  | .add a b => max (chain a + 1) (chain b)
  | .sub a b => max (chain a + 1) (chain b)
  | .mul a b => max (chain a + 1) (chain b)
  | .let_ v b => max (chain v) (chain b)
  | .call b as => max (chain b) (chain as)
  | .anil => 0
  | .acons e r => max (chain e) (chain r)

/-- **the limits of Lean's elaborator**, stated on the elaborated program -/
def LeanLimits (src : List UInt8) : Prop :=
  ∀ p, nanoElab src = some p → nest p.2 ≤ 400 ∧ chain p.2 ≤ 2500

/-- a smaller domain -/
theorem SelfHosted.mono {B : List (BitVec 32)} {space : Nat → Nat} {D D' : List UInt8 → Prop}
    {compile : Prog → Option CompiledA} (h : SelfHosted B space D compile) (hD : ∀ s, D' s → D s) :
    SelfHosted B space D' compile where
  code := h.code
  emits src p c hd := h.emits src p c (hD src hd)
  correct := h.correct
  correctInt := h.correctInt
  runs := h.runs

end Nano.SelfHost
