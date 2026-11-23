-- DENOTES-3: a data λ in a stored statement (regime check, Bridge.Real.LamDemo)
def g (x : Nat) : Nat := (fun y : Nat => Nat.succ y) x
theorem g_eq : ∀ x : Nat, g x = (fun y : Nat => Nat.succ y) x := fun _ => rfl
theorem ne12 : Nat.succ Nat.zero = Nat.succ (Nat.succ Nat.zero) → False := fun h => Nat.noConfusion h (fun h' => Nat.noConfusion h')
