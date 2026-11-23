def f (x : UInt64) : UInt64 := x + 1
theorem f_eq : ∀ x, f x = x + 1 := fun _ => rfl
