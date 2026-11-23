-- DENOTES-3 step 2 and 3a: the exported programs (Lean 4.35.0-rc3)
def f (x : Nat) : Nat := x + 1
theorem f_eq : ∀ x : Nat, f x = Nat.succ x := fun _ => rfl
theorem f_body : ∀ x : Nat, f x = x + 1 := fun _ => rfl
theorem add_one : ∀ x : Nat, x + 1 = Nat.succ x := fun _ => rfl
theorem outParam_eq : outParam.{2} Type = Type := rfl
