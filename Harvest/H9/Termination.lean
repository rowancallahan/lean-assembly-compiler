/- Harvest/H9/Termination: nano-style `termination_by` decrease rules against Lean's `measure` / `Prod.Lex` /
`WellFounded.fix` (Init/WF.lean: `measure` :267, `invImage` :189, `Prod.Lex` :286). Standalone: Init only. -/
namespace H9

/-- candidate rule: a recursive call from arguments `a` to `b` is accepted when the Nat measure strictly drops -/
def decr (f : α → Nat) (b a : α) : Bool := decide (f b < f a)

/-- nano-accepted decrease ⇒ the step is in Lean's `measure f` relation (`termination_by f x`, `decreasing_by` goal) -/
theorem decr_measure (f : α → Nat) (b a : α) (h : decr f b a = true) : (measure f).rel b a := by
  have : f b < f a := by simpa [decr] using h
  exact this

/-- hence every nano-accepted measure is well-founded in Lean's sense (what `WellFounded.fix` needs) -/
theorem decr_wf (f : α → Nat) : WellFounded (fun b a => decr f b a = true) :=
  Subrelation.wf (fun {b a} h => decr_measure f b a h) (measure f).wf

/-- the common case `n+1 → n` (structural-style recursion through `termination_by n`) -/
theorem decr_pred (n : Nat) : decr id n (n + 1) = true := by simp [decr]

/-- lexicographic pair `termination_by (a, b)`: candidate rule = first drops, or first equal and second drops -/
def lexDecr (b' a' b a : Nat) : Bool := decide (a' < a ∨ (a' = a ∧ b' < b))

theorem lexDecr_lex (a' b' a b : Nat) (h : lexDecr b' a' b a = true) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  simp only [lexDecr, decide_eq_true_eq] at h
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

/-- Lean's fixpoint equation for a measure-decreasing function, instantiated: `WellFounded.fix` unfolds -/
theorem fix_unfolds (f : Nat → Nat) (F : (x : Nat) → ((y : Nat) → (measure f).rel y x → Nat) → Nat) (x : Nat) :
    (measure f).wf.fix F x = F x (fun y _ => (measure f).wf.fix F y) :=
  WellFounded.fix_eq _ _ _

end H9
