/- Stored theorems requested by DENOTES-2, stated exactly (core Lean only, level-monomorphic). -/
abbrev Buf := List UInt64
theorem nat_z : ∀ (R : Type) (z : R) (s : Nat → R), Nat.casesOn (motive := fun _ => R) Nat.zero z s = z := fun _ _ _ => rfl
theorem nat_s : ∀ (R : Type) (z : R) (s : Nat → R) (n : Nat), Nat.casesOn (motive := fun _ => R) (Nat.succ n) z s = s n := fun _ _ _ _ => rfl
theorem prod_c : ∀ (A B R : Type) (f : A → B → R) (a : A) (b : B), @Prod.casesOn A B (fun _ => R) (Prod.mk a b) f = f a b := fun _ _ _ _ _ _ => rfl
theorem br_litN : ∀ n : Nat, @OfNat.ofNat Nat n (instOfNatNat n) = n := fun _ => rfl
theorem add0 : ∀ n : Nat, n + Nat.zero = n := fun _ => rfl
theorem addS : ∀ n m : Nat, n + Nat.succ m = Nat.succ (n + m) := fun _ _ => rfl
theorem outParam_eq : outParam.{2} Type = Type := rfl
theorem buf_eq : Buf = List UInt64 := rfl
theorem br_add : ∀ a b : Nat, UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) :=
  fun a b => (UInt64.ofNat_add a b).symm
theorem br_wrap : ∀ n : Nat, UInt64.ofNat (n + 18446744073709551616) = UInt64.ofNat n := by
  intro n
  have h : ∀ k : Nat, k = 2^64 → UInt64.ofNat (n + k) = UInt64.ofNat n := by
    intro k hk
    subst hk
    rw [← UInt64.ofNat_mod_size (x := n + 2^64), ← UInt64.ofNat_mod_size (x := n), Nat.add_mod_right]
  exact h _ (by decide)
set_option pp.all true
#print nat_z
#print nat_s
#print prod_c
#print br_litN
#print add0
#print addS
#print outParam_eq
#print buf_eq
#check @ite
#check @Nat.casesOn
#check @Prod.casesOn
#check @HAdd.hAdd
#check @instDecidableEqBool
#check @OfNat.ofNat
#print axioms br_wrap
#print axioms nat_z
