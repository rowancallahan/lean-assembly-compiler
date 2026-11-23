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


/-! # Set-level lemmas (style of `add_u64`), abstract over an application operation `app : V → V → V`.
They need no con-leche import: every field of `NatEqs` is the set-level image of one theorem above, i.e. exactly
what `transfer` yields from it (restricted to canonical numerals `nat k`, which are in `⟦Nat⟧`).  `ite`/`cond`
fields quantify over all `t e` (they are `⟦R⟧`-members in use). -/
theorem u_surj (x : UInt64) : ∃ a, x = UInt64.ofNat a := ⟨x.toNat, (UInt64.ofNat_toNat).symm⟩

namespace SetLevel
structure NatEqs (V : Type) where
  app : V → V → V
  Z : V
  S : V
  ADD : V
  SUB : V
  PRED : V
  MUL : V
  BEQ : V
  BLE : V
  MOD : V
  DIV : V
  BT : V
  BF : V
  LAND : V
  LOR : V
  SHL : V
  SHR : V
  COND : V → V → V → V           -- cond applied to its type argument `Nat`: COND c t e
  pred0 : app PRED Z = Z
  predS : ∀ x, app PRED (app S x) = x
  condT : ∀ t e, COND BT t e = t
  condF : ∀ t e, COND BF t e = e

variable {V : Type} (N : NatEqs V)

def NatEqs.nat (N : NatEqs V) : Nat → V
  | 0 => N.Z
  | k + 1 => N.app N.S (N.nat k)
def NatEqs.bl (N : NatEqs V) (c : Bool) : V := if c then N.BT else N.BF

theorem NatEqs.cond_bl (N : NatEqs V) (c : Bool) (t e : V) : N.COND (N.bl c) t e = if c then t else e := by
  cases c
  · exact N.condF t e
  · exact N.condT t e

/-- the set-level `Nat` equations, one per theorem `br_add0 … br_ble0`, at canonical numerals -/
structure NatRec (N : NatEqs V) : Prop where
  add0 : ∀ a, N.app (N.app N.ADD (N.nat a)) N.Z = N.nat a
  addS : ∀ a b, N.app (N.app N.ADD (N.nat a)) (N.app N.S (N.nat b)) = N.app N.S (N.app (N.app N.ADD (N.nat a)) (N.nat b))
  sub0 : ∀ a, N.app (N.app N.SUB (N.nat a)) N.Z = N.nat a
  subS : ∀ a b, N.app (N.app N.SUB (N.nat a)) (N.app N.S (N.nat b)) = N.app N.PRED (N.app (N.app N.SUB (N.nat a)) (N.nat b))
  mul0 : ∀ a, N.app (N.app N.MUL (N.nat a)) N.Z = N.Z
  mulS : ∀ a b, N.app (N.app N.MUL (N.nat a)) (N.app N.S (N.nat b)) = N.app (N.app N.ADD (N.app (N.app N.MUL (N.nat a)) (N.nat b))) (N.nat a)
  beq00 : N.app (N.app N.BEQ N.Z) N.Z = N.BT
  beq0S : ∀ b, N.app (N.app N.BEQ N.Z) (N.app N.S (N.nat b)) = N.BF
  beqS0 : ∀ a, N.app (N.app N.BEQ (N.app N.S (N.nat a))) N.Z = N.BF
  beqSS : ∀ a b, N.app (N.app N.BEQ (N.app N.S (N.nat a))) (N.app N.S (N.nat b)) = N.app (N.app N.BEQ (N.nat a)) (N.nat b)
  ble0 : ∀ b, N.app (N.app N.BLE N.Z) (N.nat b) = N.BT
  bleS0 : ∀ a, N.app (N.app N.BLE (N.app N.S (N.nat a))) N.Z = N.BF
  bleSS : ∀ a b, N.app (N.app N.BLE (N.app N.S (N.nat a))) (N.app N.S (N.nat b)) = N.app (N.app N.BLE (N.nat a)) (N.nat b)
  mod_ : ∀ n m, N.app (N.app N.MOD (N.nat n)) (N.nat m) =
    N.COND (N.app (N.app N.BLE (N.nat m)) (N.nat n))
      (N.COND (N.app (N.app N.BEQ (N.nat m)) N.Z) (N.nat n) (N.app (N.app N.MOD (N.app (N.app N.SUB (N.nat n)) (N.nat m))) (N.nat m)))
      (N.nat n)
  div_ : ∀ n m, N.app (N.app N.DIV (N.nat n)) (N.nat m) =
    N.COND (N.app (N.app N.BLE (N.nat m)) (N.nat n))
      (N.COND (N.app (N.app N.BEQ (N.nat m)) N.Z) N.Z (N.app N.S (N.app (N.app N.DIV (N.app (N.app N.SUB (N.nat n)) (N.nat m))) (N.nat m))))
      N.Z

variable {N} (R : NatRec N)
include R

theorem nat_add : ∀ a b, N.app (N.app N.ADD (N.nat a)) (N.nat b) = N.nat (a + b) := by
  intro a b
  induction b with
  | zero => exact R.add0 a
  | succ b ih => rw [NatEqs.nat, R.addS, ih]; rfl

theorem nat_mul : ∀ a b, N.app (N.app N.MUL (N.nat a)) (N.nat b) = N.nat (a * b) := by
  intro a b
  induction b with
  | zero => exact R.mul0 a
  | succ b ih => rw [NatEqs.nat, R.mulS, ih, nat_add R]; rfl

theorem nat_sub : ∀ a b, N.app (N.app N.SUB (N.nat a)) (N.nat b) = N.nat (a - b) := by
  intro a b
  induction b with
  | zero => exact R.sub0 a
  | succ b ih =>
    rw [NatEqs.nat, R.subS, ih]
    show N.app N.PRED (N.nat (a - b)) = N.nat (Nat.pred (a - b))
    cases a - b
    · exact N.pred0
    · exact N.predS _

theorem nat_beq : ∀ a b, N.app (N.app N.BEQ (N.nat a)) (N.nat b) = N.bl (Nat.beq a b) := by
  intro a
  induction a with
  | zero => intro b; cases b <;> simp [NatEqs.nat, NatEqs.bl, R.beq00, R.beq0S, Nat.beq]
  | succ a ih => intro b; cases b <;> simp_all [NatEqs.nat, NatEqs.bl, R.beqS0, R.beqSS, Nat.beq]

theorem nat_ble : ∀ a b, N.app (N.app N.BLE (N.nat a)) (N.nat b) = N.bl (Nat.ble a b) := by
  intro a
  induction a with
  | zero => intro b; rw [NatEqs.nat, R.ble0, br_ble0]; rfl
  | succ a ih => intro b; cases b <;> simp_all [NatEqs.nat, NatEqs.bl, R.bleS0, R.bleSS, Nat.ble]

theorem nat_mod : ∀ n m, N.app (N.app N.MOD (N.nat n)) (N.nat m) = N.nat (n % m) := by
  intro n m
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [R.mod_, nat_sub R, nat_ble R, show N.Z = N.nat 0 from rfl, nat_beq R, NatEqs.cond_bl, NatEqs.cond_bl, br_mod n m]
    cases h1 : Nat.ble m n <;> cases h2 : Nat.beq m 0 <;> simp
    have hm : m ≠ 0 := fun h => by simp [h] at h2
    have hle : m ≤ n := by simpa [Nat.ble_eq] using h1
    exact ih (n - m) (by omega)

theorem nat_div : ∀ n m, N.app (N.app N.DIV (N.nat n)) (N.nat m) = N.nat (n / m) := by
  intro n m
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [R.div_, nat_sub R, nat_ble R, show N.Z = N.nat 0 from rfl, nat_beq R, NatEqs.cond_bl, NatEqs.cond_bl, br_div n m]
    cases h1 : Nat.ble m n <;> cases h2 : Nat.beq m 0 <;> simp
    have hm : m ≠ 0 := fun h => by simp [h] at h2
    have hle : m ≤ n := by simpa [Nat.ble_eq] using h1
    rw [ih (n - m) (by omega)]; rfl

/-- bit operations, shifts: the set-level image of `br_land0/br_land_rec/br_lor0/br_lor_rec/br_shl*/br_shr*` -/
structure BitRec (N : NatEqs V) : Prop where
  land0 : ∀ m, N.app (N.app N.LAND N.Z) (N.nat m) = N.Z
  landR : ∀ n m, N.app (N.app N.LAND (N.nat n)) (N.nat m) =
    N.app (N.app N.ADD (N.app (N.app N.MUL (N.nat 2)) (N.app (N.app N.LAND (N.app (N.app N.DIV (N.nat n)) (N.nat 2))) (N.app (N.app N.DIV (N.nat m)) (N.nat 2)))))
      (N.app (N.app N.MUL (N.app (N.app N.MOD (N.nat n)) (N.nat 2))) (N.app (N.app N.MOD (N.nat m)) (N.nat 2)))
  lor0 : ∀ m, N.app (N.app N.LOR N.Z) (N.nat m) = N.nat m
  lorR : ∀ n m, N.app (N.app N.LOR (N.nat n)) (N.nat m) =
    N.app (N.app N.ADD (N.app (N.app N.MUL (N.nat 2)) (N.app (N.app N.LOR (N.app (N.app N.DIV (N.nat n)) (N.nat 2))) (N.app (N.app N.DIV (N.nat m)) (N.nat 2)))))
      (N.app (N.app N.SUB (N.app (N.app N.ADD (N.app (N.app N.MOD (N.nat n)) (N.nat 2))) (N.app (N.app N.MOD (N.nat m)) (N.nat 2))))
        (N.app (N.app N.MUL (N.app (N.app N.MOD (N.nat n)) (N.nat 2))) (N.app (N.app N.MOD (N.nat m)) (N.nat 2))))
  shl0 : ∀ n, N.app (N.app N.SHL (N.nat n)) N.Z = N.nat n
  shlS : ∀ n m, N.app (N.app N.SHL (N.nat n)) (N.app N.S (N.nat m)) = N.app (N.app N.MUL (N.nat 2)) (N.app (N.app N.SHL (N.nat n)) (N.nat m))
  shr0 : ∀ n, N.app (N.app N.SHR (N.nat n)) N.Z = N.nat n
  shrS : ∀ n m, N.app (N.app N.SHR (N.nat n)) (N.app N.S (N.nat m)) = N.app (N.app N.DIV (N.app (N.app N.SHR (N.nat n)) (N.nat m))) (N.nat 2)

section Bits
variable (B : BitRec N)
include B

omit R B in
theorem nat_two : N.nat 2 = N.app N.S (N.app N.S N.Z) := rfl

theorem nat_shl : ∀ n k, N.app (N.app N.SHL (N.nat n)) (N.nat k) = N.nat (n <<< k) := by
  intro n k
  induction k with
  | zero => exact B.shl0 n
  | succ k ih => rw [NatEqs.nat, B.shlS, ih, nat_mul R, Nat.shiftLeft_succ]

theorem nat_shr : ∀ n k, N.app (N.app N.SHR (N.nat n)) (N.nat k) = N.nat (n >>> k) := by
  intro n k
  induction k with
  | zero => exact B.shr0 n
  | succ k ih => rw [NatEqs.nat, B.shrS, ih, nat_div R, Nat.shiftRight_succ]

theorem nat_land : ∀ n m, N.app (N.app N.LAND (N.nat n)) (N.nat m) = N.nat (n &&& m) := by
  intro n m
  induction n using Nat.strongRecOn generalizing m with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; rw [show N.nat 0 = N.Z from rfl, B.land0, Nat.zero_and]; rfl
    · rw [B.landR]
      simp only [nat_div R, nat_mod R, ih (n / 2) (by omega), nat_mul R, nat_add R]
      exact congrArg N.nat (br_land_rec n m).symm

theorem nat_lor : ∀ n m, N.app (N.app N.LOR (N.nat n)) (N.nat m) = N.nat (n ||| m) := by
  intro n m
  induction n using Nat.strongRecOn generalizing m with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; rw [show N.nat 0 = N.Z from rfl, B.lor0, Nat.zero_or]
    · rw [B.lorR]
      simp only [nat_div R, nat_mod R, ih (n / 2) (by omega), nat_mul R, nat_add R, nat_sub R]
      exact congrArg N.nat (br_lor_rec n m).symm

end Bits

/-! ## UInt64 at the set level.  Encoding `u x = OF (nat x.toNat)`; each field is the set-level image of the
named theorem (`OF = ⟦UInt64.ofNat⟧`, the `*64` heads are `⟦@HAdd.hAdd UInt64 UInt64 UInt64 (instHAdd ..)⟧` etc.). -/
structure U64Rec (N : NatEqs V) where
  OF : V
  ADD64 : V
  SUB64 : V
  MUL64 : V
  AND64 : V
  OR64 : V
  SHL64 : V
  SHR64 : V
  BEQ64 : V
  ITELT : V → V → V → V → V      -- `⟦ite R (a < b) (UInt64.decLt a b)⟧` as a function of the operand sets and t e
  wrap : ∀ n, N.app OF (N.app (N.app N.ADD (N.nat n)) (N.nat 18446744073709551616)) = N.app OF (N.nat n)
  add : ∀ a b, N.app (N.app ADD64 (N.app OF (N.nat a))) (N.app OF (N.nat b)) = N.app OF (N.app (N.app N.ADD (N.nat a)) (N.nat b))
  mul : ∀ a b, N.app (N.app MUL64 (N.app OF (N.nat a))) (N.app OF (N.nat b)) = N.app OF (N.app (N.app N.MUL (N.nat a)) (N.nat b))
  sub : ∀ a b, N.app (N.app SUB64 (N.app OF (N.nat a))) (N.app OF (N.nat b)) =
    N.app OF (N.app (N.app N.ADD (N.nat a)) (N.app (N.app N.SUB (N.app (N.app N.MUL (N.nat 18446744073709551616)) (N.nat b))) (N.nat b)))
  and : ∀ a b, N.app (N.app AND64 (N.app OF (N.nat a))) (N.app OF (N.nat b)) = N.app OF (N.app (N.app N.LAND (N.nat a)) (N.nat b))
  or : ∀ a b, N.app (N.app OR64 (N.app OF (N.nat a))) (N.app OF (N.nat b)) = N.app OF (N.app (N.app N.LOR (N.nat a)) (N.nat b))
  shl : ∀ a b, N.app (N.app SHL64 (N.app OF (N.nat a))) (N.app OF (N.nat b)) =
    N.app OF (N.app (N.app N.SHL (N.nat a)) (N.app (N.app N.MOD (N.nat b)) (N.nat 64)))
  shr : ∀ a b, N.app (N.app SHR64 (N.app OF (N.nat a))) (N.app OF (N.nat b)) =
    N.app OF (N.app (N.app N.SHR (N.app (N.app N.MOD (N.nat a)) (N.nat 18446744073709551616))) (N.app (N.app N.MOD (N.nat b)) (N.nat 64)))
  beq : ∀ a b, N.app (N.app BEQ64 (N.app OF (N.nat a))) (N.app OF (N.nat b)) =
    N.app (N.app N.BEQ (N.app (N.app N.MOD (N.nat a)) (N.nat 18446744073709551616))) (N.app (N.app N.MOD (N.nat b)) (N.nat 18446744073709551616))
  lt : ∀ a b t e, ITELT (N.app OF (N.nat a)) (N.app OF (N.nat b)) t e =
    N.COND (N.app (N.app N.BLE (N.app (N.app N.ADD (N.app (N.app N.MOD (N.nat a)) (N.nat 18446744073709551616))) (N.nat 1)))
      (N.app (N.app N.MOD (N.nat b)) (N.nat 18446744073709551616))) t e

variable (U : U64Rec N)
include R U
def u (x : UInt64) : V := N.app U.OF (N.nat x.toNat)

theorem of_mod : ∀ n, N.app U.OF (N.nat n) = N.app U.OF (N.nat (n % 18446744073709551616)) := by
  have hk : ∀ n k, N.app U.OF (N.nat (n + 18446744073709551616 * k)) = N.app U.OF (N.nat n) := by
    intro n k
    induction k with
    | zero => rfl
    | succ k ih =>
      have h := U.wrap (n + 18446744073709551616 * k)
      rw [nat_add R] at h
      rw [show n + 18446744073709551616 * (k + 1) = n + 18446744073709551616 * k + 18446744073709551616 by omega, h, ih]
  intro n
  have h := hk (n % 18446744073709551616) (n / 18446744073709551616)
  rw [Nat.mod_add_div] at h
  exact h

theorem u_ofNat : ∀ n, u U (UInt64.ofNat n) = N.app U.OF (N.nat n) := by
  intro n
  simp only [u, UInt64.toNat_ofNat']
  exact (of_mod R U n).symm

theorem u64_add : ∀ x y : UInt64, N.app (N.app U.ADD64 (u U x)) (u U y) = u U (x + y) := by
  intro x y
  obtain ⟨a, rfl⟩ := _root_.u_surj x; obtain ⟨b, rfl⟩ := _root_.u_surj y
  rw [u_ofNat R U, u_ofNat R U, U.add, nat_add R, br_add, u_ofNat R U]

theorem u64_mul : ∀ x y : UInt64, N.app (N.app U.MUL64 (u U x)) (u U y) = u U (x * y) := by
  intro x y
  obtain ⟨a, rfl⟩ := _root_.u_surj x; obtain ⟨b, rfl⟩ := _root_.u_surj y
  rw [u_ofNat R U, u_ofNat R U, U.mul, nat_mul R, br_mul, u_ofNat R U]

theorem u64_sub : ∀ x y : UInt64, N.app (N.app U.SUB64 (u U x)) (u U y) = u U (x - y) := by
  intro x y
  obtain ⟨a, rfl⟩ := _root_.u_surj x; obtain ⟨b, rfl⟩ := _root_.u_surj y
  rw [u_ofNat R U, u_ofNat R U, U.sub, nat_mul R, nat_sub R, nat_add R, br_sub, u_ofNat R U]

theorem u64_beq : ∀ x y : UInt64, N.app (N.app U.BEQ64 (u U x)) (u U y) = N.bl (x == y) := by
  intro x y
  obtain ⟨a, rfl⟩ := _root_.u_surj x; obtain ⟨b, rfl⟩ := _root_.u_surj y
  rw [u_ofNat R U, u_ofNat R U, U.beq, nat_mod R, nat_mod R, nat_beq R, br_beq64]

theorem u64_lt : ∀ (x y : UInt64) (t e : V), U.ITELT (u U x) (u U y) t e = if x < y then t else e := by
  intro x y t e
  obtain ⟨a, rfl⟩ := _root_.u_surj x; obtain ⟨b, rfl⟩ := _root_.u_surj y
  rw [u_ofNat R U, u_ofNat R U, U.lt, nat_mod R, nat_mod R, nat_add R, nat_ble R, NatEqs.cond_bl, br_lt64 V a b t e]
  cases Nat.ble (a % 18446744073709551616 + 1) (b % 18446744073709551616) <;> rfl

section Bits
variable (B : BitRec N)
include B
theorem u64_and : ∀ x y : UInt64, N.app (N.app U.AND64 (u U x)) (u U y) = u U (x &&& y) := by
  intro x y
  obtain ⟨a, rfl⟩ := _root_.u_surj x; obtain ⟨b, rfl⟩ := _root_.u_surj y
  rw [u_ofNat R U, u_ofNat R U, U.and, nat_land R B, br_and, u_ofNat R U]

theorem u64_or : ∀ x y : UInt64, N.app (N.app U.OR64 (u U x)) (u U y) = u U (x ||| y) := by
  intro x y
  obtain ⟨a, rfl⟩ := _root_.u_surj x; obtain ⟨b, rfl⟩ := _root_.u_surj y
  rw [u_ofNat R U, u_ofNat R U, U.or, nat_lor R B, br_or, u_ofNat R U]

theorem u64_shl : ∀ x y : UInt64, N.app (N.app U.SHL64 (u U x)) (u U y) = u U (x <<< y) := by
  intro x y
  obtain ⟨a, rfl⟩ := _root_.u_surj x; obtain ⟨b, rfl⟩ := _root_.u_surj y
  rw [u_ofNat R U, u_ofNat R U, U.shl, nat_mod R, nat_shl R B, br_shl, u_ofNat R U]

theorem u64_shr : ∀ x y : UInt64, N.app (N.app U.SHR64 (u U x)) (u U y) = u U (x >>> y) := by
  intro x y
  obtain ⟨a, rfl⟩ := _root_.u_surj x; obtain ⟨b, rfl⟩ := _root_.u_surj y
  rw [u_ofNat R U, u_ofNat R U, U.shr, nat_mod R, nat_mod R, nat_shr R B, br_shr, u_ofNat R U]
end Bits

end SetLevel

#print axioms br_sub
#print axioms br_shl
#print axioms br_shr
#print axioms br_beq64
#print axioms br_lt64
#print axioms br_ltN
#print axioms br_mod
#print axioms br_land_rec
#print axioms SetLevel.nat_mod
#print axioms SetLevel.nat_land
#print axioms SetLevel.u64_add
#print axioms SetLevel.u64_sub
#print axioms SetLevel.u64_lt
#print axioms SetLevel.u64_shr
#print axioms SetLevel.u64_or
