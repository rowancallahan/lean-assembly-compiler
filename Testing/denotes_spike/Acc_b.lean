def f (x : UInt64) : UInt64 := if x = 0 then 1 else x + 1
theorem f_ite : ∀ x, f x = if x = 0 then 1 else x + 1 := fun _ => rfl
