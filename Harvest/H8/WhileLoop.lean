/- Harvest/H8/WhileLoop: `while c do x := f x` (Lean: `Lean.Loop.forIn`, built on the `partial` `repeatM`, Init/While.lean:95) against a
fuel-bounded nano executor, subset form: if nano's run finishes within its fuel, Lean's loop returns the same value.
The bridge is Lean's own unfolding theorem `Lean.Loop.forIn_eq_of_monadTail` (Init/Internal/Order/While.lean:50), valid for `Id`. -/
import Init.Internal.Order.While
namespace H8

/-- candidate: run `g` at most `n` times; `none` = out of fuel (nano refuses such a loop) -/
def runW {β} (g : β → ForInStep β) : Nat → β → Option β
  | 0, _ => none
  | n + 1, b => match g b with
    | .done b' => some b'
    | .yield b' => runW g n b'

/-- **subset form**: a nano run that finishes is Lean's `Loop.forIn` value (the loop Lean's `while`/`repeat` runs on, in `Id`) -/
theorem runW_imp_lean {β} (g : β → ForInStep β) (n : Nat) (b r : β) (h : runW g n b = some r) :
    Id.run (Lean.Loop.forIn ⟨⟩ b (fun _ b => (pure (g b) : Id (ForInStep β)))) = r := by
  induction n generalizing b with
  | zero => simp [runW] at h
  | succ n ih =>
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [runW] at h
    cases hg : g b <;> simp_all [Id.run] <;> rfl

/-- `while c x do x := f x` (the `x` is the single mutable variable): the body of the loop Lean builds is `if c x then yield (f x) else done x` -/
def whileStep {β} (c : β → Bool) (f : β → β) (b : β) : ForInStep β := if c b then .yield (f b) else .done b

theorem while_lean {β} (c : β → Bool) (f : β → β) (a r : β) (n : Nat) (h : runW (whileStep c f) n a = some r) :
    (Id.run do
      let mut x := a
      while c x do x := f x
      return x) = r := by
  have := runW_imp_lean (whileStep c f) n a r h
  simp only [whileStep] at this
  refine Eq.trans ?_ this
  rfl

end H8
