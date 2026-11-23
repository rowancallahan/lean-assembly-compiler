/- Bridge prelude, UInt64 + Nat part (S1).  Core Lean only (Lean 4.35.0-rc3, no imports).
Statement shapes follow nano's emitted spelling; all binders are `Nat` (the set-level encoding of a UInt64 is
`UInt64.ofNat (nat k)`, k < 2^64).  `2^64` is the literal 18446744073709551616 everywhere. -/

/-! ## UInt64 arithmetic: `ofNat` form -/
theorem br_add : ∀ a b : Nat, UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) :=
  fun a b => (UInt64.ofNat_add a b).symm
theorem br_mul : ∀ a b : Nat, UInt64.ofNat a * UInt64.ofNat b = UInt64.ofNat (a * b) :=
  fun a b => (UInt64.ofNat_mul a b).symm
theorem br_wrap : ∀ n : Nat, UInt64.ofNat (n + 18446744073709551616) = UInt64.ofNat n := by
  intro n
  have h : ∀ k : Nat, k = 2^64 → UInt64.ofNat (n + k) = UInt64.ofNat n := by
    intro k hk
    subst hk
    rw [← UInt64.ofNat_mod_size (x := n + 2^64), ← UInt64.ofNat_mod_size (x := n), Nat.add_mod_right]
  exact h _ (by decide)
/-- sub: `a - b = a + (2^64·b - b)` mod 2^64 (no `%`, no hypothesis; only Nat add/mul/sub at set level) -/
theorem br_sub : ∀ a b : Nat, UInt64.ofNat a - UInt64.ofNat b =
    UInt64.ofNat (a + (18446744073709551616 * b - b)) := by
  intro a b
  have h1 : a + (18446744073709551616 * b - b) = (a + 18446744073709551616 * b) - b := by omega
  have h2 : ∀ k : Nat, UInt64.ofNat (a + 18446744073709551616 * k) = UInt64.ofNat a := by
    intro k
    rw [← UInt64.ofNat_mod_size (x := a + _), ← UInt64.ofNat_mod_size (x := a)]
    congr 1
    exact Nat.add_mul_mod_self_left a _ k
  rw [h1, UInt64.ofNat_sub (by omega), h2]
theorem br_and : ∀ a b : Nat, UInt64.ofNat a &&& UInt64.ofNat b = UInt64.ofNat (a &&& b) :=
  fun a b => (UInt64.ofNat_and a b).symm
theorem br_or : ∀ a b : Nat, UInt64.ofNat a ||| UInt64.ofNat b = UInt64.ofNat (a ||| b) :=
  fun a b => (UInt64.ofNat_or a b).symm
theorem br_shl : ∀ a b : Nat, UInt64.ofNat a <<< UInt64.ofNat b = UInt64.ofNat (a <<< (b % 64)) := by
  intro a b
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_shiftLeft]
  simp [Nat.shiftLeft_eq, Nat.mod_mul_mod]
theorem br_shr : ∀ a b : Nat, UInt64.ofNat a >>> UInt64.ofNat b = UInt64.ofNat ((a % 18446744073709551616) >>> (b % 64)) := by
  intro a b
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_shiftRight]
  simp
  refine (Nat.mod_eq_of_lt ?_).symm
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide))
theorem and_mod2 (n m : Nat) : (n &&& m) % 2 = n % 2 * (m % 2) := by
  have h := Nat.testBit_and n m 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one n with h1 | h1 <;> rcases Nat.mod_two_eq_zero_or_one m with h2 | h2 <;>
    rcases Nat.mod_two_eq_zero_or_one (n &&& m) with h3 | h3 <;> simp_all
theorem or_mod2 (n m : Nat) : (n ||| m) % 2 = n % 2 + m % 2 - n % 2 * (m % 2) := by
  have h := Nat.testBit_or n m 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one n with h1 | h1 <;> rcases Nat.mod_two_eq_zero_or_one m with h2 | h2 <;>
    rcases Nat.mod_two_eq_zero_or_one (n ||| m) with h3 | h3 <;> simp_all
theorem br_land_rec : ∀ n m : Nat, n &&& m = 2 * (n / 2 &&& m / 2) + n % 2 * (m % 2) := by
  intro n m
  rw [← and_mod2, ← Nat.and_div_two]; omega
theorem br_lor_rec : ∀ n m : Nat, n ||| m = 2 * (n / 2 ||| m / 2) + (n % 2 + m % 2 - n % 2 * (m % 2)) := by
  intro n m
  rw [← or_mod2, ← Nat.or_div_two]; omega
theorem br_land0 : ∀ m : Nat, 0 &&& m = 0 := Nat.zero_and
theorem br_lor0 : ∀ m : Nat, 0 ||| m = m := Nat.zero_or

/-! ## UInt64 comparisons and `ite` (nano's spelling: `ite R (a < b) (UInt64.decLt a b) t e`,
`ite R (BEq.beq a b = true) (instDecidableEqBool (a == b) true) t e`) -/
theorem br_cond_t : ∀ (R : Type) (t e : R), cond true t e = t := fun _ _ _ => rfl
theorem br_cond_f : ∀ (R : Type) (t e : R), cond false t e = e := fun _ _ _ => rfl
theorem br_ite_cond : ∀ (R : Type) (c : Bool) (t e : R),
    @ite R (c = true) (instDecidableEqBool c true) t e = cond c t e := by
  intro R c t e; cases c <;> rfl
theorem br_ite_t : ∀ (R : Type) (t e : R), @ite R (true = true) (instDecidableEqBool true true) t e = t :=
  fun _ _ _ => rfl
theorem br_ite_f : ∀ (R : Type) (t e : R), @ite R (false = true) (instDecidableEqBool false true) t e = e :=
  fun _ _ _ => rfl
theorem br_beq64 : ∀ a b : Nat, (UInt64.ofNat a == UInt64.ofNat b) =
    Nat.beq (a % 18446744073709551616) (b % 18446744073709551616) := by
  intro a b
  have h : ∀ x y : Nat, (UInt64.ofNat x == UInt64.ofNat y) = Nat.beq (x % 18446744073709551616) (y % 18446744073709551616) := by
    intro x y
    show decide (UInt64.ofNat x = UInt64.ofNat y) = _
    rw [Bool.eq_iff_iff]
    simp [← UInt64.toNat_inj]
  exact h a b
theorem br_lt64 : ∀ (R : Type) (a b : Nat) (t e : R),
    @ite R (UInt64.ofNat a < UInt64.ofNat b) (UInt64.decLt (UInt64.ofNat a) (UInt64.ofNat b)) t e =
    cond (Nat.ble (a % 18446744073709551616 + 1) (b % 18446744073709551616)) t e := by
  intro R a b t e
  have h : (UInt64.ofNat a < UInt64.ofNat b) ↔ Nat.ble (a % 18446744073709551616 + 1) (b % 18446744073709551616) = true := by
    simp [UInt64.lt_iff_toNat_lt, Nat.ble_eq, Nat.succ_le_iff]
  cases hb : Nat.ble (a % 18446744073709551616 + 1) (b % 18446744073709551616)
  · rw [hb] at h; exact if_neg (fun hl => by simp_all)
  · rw [hb] at h; exact if_pos (h.2 rfl)
/-! ## Nat comparisons in fuel position -/
theorem br_beqN : ∀ a b : Nat, (@BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b) = Nat.beq a b := by
  intro a b
  rw [Bool.eq_iff_iff]; simp [Nat.beq_eq]
theorem br_ltN : ∀ (R : Type) (a b : Nat) (t e : R),
    @ite R (a < b) (Nat.decLt a b) t e = cond (Nat.ble (a + 1) b) t e := by
  intro R a b t e
  have h : a < b ↔ Nat.ble (a + 1) b = true := by simp [Nat.ble_eq, Nat.succ_le_iff]
  cases hb : Nat.ble (a + 1) b
  · rw [hb] at h; exact if_neg (fun hl => by simp_all)
  · rw [hb] at h; exact if_pos (h.2 rfl)

/-! ## Nat: literals and recursion equations (all `rfl` / core) -/
theorem br_lit : ∀ n : Nat, (@OfNat.ofNat UInt64 n (@UInt64.instOfNat n)) = UInt64.ofNat n :=
  fun _ => rfl
theorem br_litN : ∀ n : Nat, (@OfNat.ofNat Nat n (instOfNatNat n)) = n := fun _ => rfl
theorem br_add0 : ∀ n : Nat, n + 0 = n := fun _ => rfl
theorem br_addsucc : ∀ n m : Nat, n + Nat.succ m = Nat.succ (n + m) := fun _ _ => rfl
theorem br_sub0 : ∀ n : Nat, n - 0 = n := fun _ => rfl
theorem br_subsucc : ∀ n m : Nat, n - Nat.succ m = Nat.pred (n - m) := fun _ _ => rfl
theorem br_pred0 : Nat.pred 0 = 0 := rfl
theorem br_predsucc : ∀ n : Nat, Nat.pred (Nat.succ n) = n := fun _ => rfl
theorem br_mul0 : ∀ n : Nat, n * 0 = 0 := fun _ => rfl
theorem br_mulsucc : ∀ n m : Nat, n * Nat.succ m = n * m + n := fun _ _ => rfl
theorem br_beq00 : Nat.beq 0 0 = true := rfl
theorem br_beq0s : ∀ m : Nat, Nat.beq 0 (Nat.succ m) = false := fun _ => rfl
theorem br_beqs0 : ∀ n : Nat, Nat.beq (Nat.succ n) 0 = false := fun _ => rfl
theorem br_beqss : ∀ n m : Nat, Nat.beq (Nat.succ n) (Nat.succ m) = Nat.beq n m := fun _ _ => rfl
theorem br_ble0 : ∀ m : Nat, Nat.ble 0 m = true := fun m => by cases m <;> rfl
theorem br_bles0 : ∀ n : Nat, Nat.ble (Nat.succ n) 0 = false := fun _ => rfl
theorem br_bless : ∀ n m : Nat, Nat.ble (Nat.succ n) (Nat.succ m) = Nat.ble n m := fun _ _ => rfl
/-- `%` and `/` have no structural equations; these two (from `Nat.mod_eq_ite` / `Nat.div_eq_ite`) are what a
set-level strong induction on `n` needs. -/
theorem br_mod : ∀ n m : Nat, n % m = cond (Nat.ble m n) (cond (Nat.beq m 0) n ((n - m) % m)) n := by
  intro n m
  rw [Nat.mod_eq_ite]
  by_cases h1 : m ≤ n <;> by_cases h2 : m = 0 <;> simp [Nat.ble_eq, Nat.beq_eq, h1, h2, Nat.pos_iff_ne_zero]
theorem br_div : ∀ n m : Nat, n / m = cond (Nat.ble m n) (cond (Nat.beq m 0) 0 ((n - m) / m + 1)) 0 := by
  intro n m
  rw [Nat.div_eq_ite]
  by_cases h1 : m ≤ n <;> by_cases h2 : m = 0 <;> simp [Nat.ble_eq, Nat.beq_eq, h1, h2, Nat.pos_iff_ne_zero]
theorem br_shl0 : ∀ n : Nat, n <<< 0 = n := fun _ => rfl
theorem br_shlsucc : ∀ n m : Nat, n <<< Nat.succ m = 2 * (n <<< m) := Nat.shiftLeft_succ
theorem br_shr0 : ∀ n : Nat, n >>> 0 = n := fun _ => rfl
theorem br_shrsucc : ∀ n m : Nat, n >>> Nat.succ m = (n >>> m) / 2 := Nat.shiftRight_succ

#print axioms br_sub
#print axioms br_shl
#print axioms br_shr
#print axioms br_beq64
#print axioms br_lt64
#print axioms br_ltN
#print axioms br_mod
#print axioms br_div
#print axioms br_land_rec
#print axioms br_lor_rec
