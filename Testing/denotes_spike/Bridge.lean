theorem br_add : ∀ a b : Nat, UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) :=
  fun a b => (UInt64.ofNat_add a b).symm
theorem br_wrap : ∀ n : Nat, UInt64.ofNat (n + 18446744073709551616) = UInt64.ofNat n := by
  intro n
  have h : ∀ k : Nat, k = 2^64 → UInt64.ofNat (n + k) = UInt64.ofNat n := by
    intro k hk
    subst hk
    rw [← UInt64.ofNat_mod_size (x := n + 2^64), ← UInt64.ofNat_mod_size (x := n), Nat.add_mod_right]
  exact h _ (by decide)
theorem br_lit : ∀ n : Nat, (@OfNat.ofNat UInt64 n (@UInt64.instOfNat n)) = UInt64.ofNat n :=
  fun _ => rfl
theorem br_ite_t : ∀ (R : Type) (t e : R), @ite R (true = true) (instDecidableEqBool true true) t e = t :=
  fun _ _ _ => rfl
theorem br_ite_f : ∀ (R : Type) (t e : R), @ite R (false = true) (instDecidableEqBool false true) t e = e :=
  fun _ _ _ => rfl
theorem br_add0 : ∀ n : Nat, n + 0 = n := fun _ => rfl
theorem br_addsucc : ∀ n m : Nat, n + Nat.succ m = Nat.succ (n + m) := fun _ _ => rfl
theorem br_len : ∀ (a : UInt8) (l : List UInt8), (a :: l).length = l.length + 1 := fun _ _ => rfl
def f : Nat → UInt64 → UInt64
  | 0, x => x
  | n+1, x => f n (x + 1)
theorem f_nano : f = fun (n : Nat) (x : UInt64) => Nat.casesOn (motive := fun _ => UInt64) n x (fun k => f k (x + 1)) := by
  funext n x
  cases n
  · rfl
  · rfl
theorem f_let : ∀ x : UInt64, (fun (y : UInt64) => y + y) x = x + x := fun _ => rfl
set_option pp.all true
#print br_add
#print br_wrap
#print br_lit
#print br_ite_t
#print br_ite_f
#print br_len
#print f_let
#print axioms f_nano
#print axioms br_wrap
