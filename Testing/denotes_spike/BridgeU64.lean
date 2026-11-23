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
