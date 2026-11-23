-- DENOTES-3 growth step "calls" (shares the ite prelude): `def m (x : List UInt8) : List UInt8 := put [] (if rd x 0 < 5 then 1 else 2)`
-- with nano's prelude `rd`, `put` and the (structural, `rfl`/core) equations the bridge reads.
def rd (xs : List UInt8) (i : UInt64) : UInt64 := (xs.getD i.toNat 0).toUInt64
def put (o : List UInt8) (b : UInt64) : List UInt8 := o ++ [b.toUInt8]
def f (a : UInt64) : UInt64 := a + 1
def len (xs : List UInt8) : UInt64 := xs.length.toUInt64
theorem len_nil : len [] = UInt64.ofNat 0 := rfl
theorem len_cons : ∀ (a : UInt8) (l : List UInt8), len (a :: l) = len l + 1 := by
  intro a l; apply UInt64.toNat_inj.mp; simp [len, Nat.add_mod]
def lp : Nat → List UInt8 → UInt64 → UInt64
  | 0, _, a => a
  | n + 1, x, a => lp n x (a + 1)
theorem lp_zero : ∀ (x : List UInt8) (a : UInt64), lp Nat.zero x a = a := fun _ _ => rfl
theorem lp_succ : ∀ (n : Nat) (x : List UInt8) (a : UInt64), lp (Nat.succ n) x a = lp n x (a + 1) := fun _ _ _ => rfl
theorem f_eq : ∀ a : UInt64, f a = a + 1 := fun _ => rfl
def m (x : List UInt8) : List UInt8 := put [] (f (rd x 0) * 2)
theorem m_eq : ∀ x : List UInt8, m x = put [] (f (rd x 0) * 2) := fun _ => rfl
theorem rd_nil0 : rd [] 0 = UInt64.ofNat 0 := rfl
theorem rd_cons0 : ∀ (a : UInt8) (l : List UInt8), rd (a :: l) 0 = a.toUInt64 := fun _ _ => rfl
theorem u8_u64 : ∀ n : Nat, (UInt8.ofNat n).toUInt64 = UInt64.ofNat (n % 256) := by
  intro n; apply UInt64.toNat_inj.mp; simp; omega
theorem lit64 : ∀ n : Nat, @OfNat.ofNat UInt64 n (UInt64.instOfNat) = UInt64.ofNat n := fun _ => rfl
theorem ite_lt : ∀ (a b : Nat) (t e : UInt64),
    @ite UInt64 (UInt64.ofNat a < UInt64.ofNat b) (UInt64.decLt (UInt64.ofNat a) (UInt64.ofNat b)) t e
      = cond (Nat.ble ((b % 18446744073709551616)) (a % 18446744073709551616)) e t := by
  intro a b t e
  have hlt : (UInt64.ofNat a < UInt64.ofNat b) ↔ a % 18446744073709551616 < b % 18446744073709551616 := by
    rw [UInt64.lt_iff_toNat_lt]; simp
  by_cases h : UInt64.ofNat a < UInt64.ofNat b
  · rw [if_pos h]
    have : Nat.ble (b % 18446744073709551616) (a % 18446744073709551616) = false := by
      have := hlt.mp h; cases hb : Nat.ble (b % 18446744073709551616) (a % 18446744073709551616) <;> simp_all [Nat.ble_eq] <;> omega
    rw [this]; rfl
  · rw [if_neg h]
    have : Nat.ble (b % 18446744073709551616) (a % 18446744073709551616) = true := by
      have := mt hlt.mpr h; rw [Nat.ble_eq]; omega
    rw [this]; rfl
theorem cond_t : ∀ (t e : UInt64), cond true t e = t := fun _ _ => rfl
theorem cond_f : ∀ (t e : UInt64), cond false t e = e := fun _ _ => rfl
theorem ble_z : ∀ m : Nat, Nat.ble Nat.zero m = true := fun _ => rfl
theorem ble_sz : ∀ n : Nat, Nat.ble (Nat.succ n) Nat.zero = false := fun _ => rfl
theorem ble_ss : ∀ n m : Nat, Nat.ble (Nat.succ n) (Nat.succ m) = Nat.ble n m := fun _ _ => rfl
theorem zero_add' : ∀ m : Nat, Nat.zero + m = m := Nat.zero_add
theorem succ_add' : ∀ n m : Nat, Nat.succ n + m = Nat.succ (n + m) := Nat.succ_add
theorem mod_small : ∀ n m : Nat, n % (n + Nat.succ m) = n := fun n m => Nat.mod_eq_of_lt (by omega)
theorem br_litN : ∀ n : Nat, @OfNat.ofNat Nat n (instOfNatNat n) = n := fun _ => rfl
theorem outParam_eq : outParam.{2} Type = Type := rfl
theorem put_nil : ∀ n : Nat, put [] (UInt64.ofNat n) = [UInt8.ofNat n] := by
  intro n; simp only [put, List.nil_append, List.cons.injEq, and_true]
  apply UInt8.toNat_inj.mp; simp
-- arithmetic prelude (UInt64 `+`/`*` through `ofNat`, Nat `*`, `%` on bytes)
theorem br_add64 : ∀ a b : Nat, UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) := by
  intro a b; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add, Nat.add_mod]
theorem br_mul64 : ∀ a b : Nat, UInt64.ofNat a * UInt64.ofNat b = UInt64.ofNat (a * b) := by
  intro a b; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_mul, Nat.mul_mod]
theorem mul_zero' : ∀ n : Nat, n * Nat.zero = Nat.zero := fun _ => rfl
theorem mul_succ' : ∀ n m : Nat, n * Nat.succ m = n * m + n := fun _ _ => rfl
theorem add_mod_right' : ∀ n m : Nat, (n + m) % m = n % m := Nat.add_mod_right
theorem u8_mod : ∀ n : Nat, UInt8.ofNat n = UInt8.ofNat (n % 256) := by
  intro n; apply UInt8.toNat_inj.mp; simp
