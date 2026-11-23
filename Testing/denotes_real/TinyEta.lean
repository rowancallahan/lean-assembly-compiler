-- DENOTES-3: does con-leche accept the pair-eta equation the generator would emit?
def g (p : UInt64 × UInt64) : UInt64 := match p with | (a, b) => a * b + a
theorem g_eq : ∀ p : UInt64 × UInt64, g p = p.1 * p.2 + p.1 := fun _ => rfl
def h (p : UInt64 × UInt64) : UInt64 := Prod.casesOn (motive := fun _ => UInt64) p (fun a b => a * b + a)
theorem h_eq : ∀ p : UInt64 × UInt64, h p = Prod.fst p * Prod.snd p + Prod.fst p := fun _ => rfl
