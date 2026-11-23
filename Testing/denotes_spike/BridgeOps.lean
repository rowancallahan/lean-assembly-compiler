/- Bridge prelude, part 2: control + data ops.  Core Lean only (exported to con-leche).  Every theorem is stated
POINTWISE (`∀ args, lhs = rhs`), proved by `rfl`/core lemmas.  The prelude defs are the List reference prelude
(Testing/nano/v2self/boot/B1L.lean), copied verbatim. -/

-- ===== the nano prelude (List variant) =====
def rd (xs : List UInt8) (i : UInt64) : UInt64 := (xs.getD i.toNat 0).toUInt64
def len (xs : List UInt8) : UInt64 := xs.length.toUInt64
def put (o : List UInt8) (b : UInt64) : List UInt8 := o ++ [b.toUInt8]
def len' (xs : List UInt8) : Nat := xs.length
abbrev Buf := List UInt64
def bnew : Buf := []
def bsize (b : Buf) : UInt64 := b.length.toUInt64
def bget (b : Buf) (i : UInt64) : UInt64 := b.getD i.toNat 0
def bset (b : Buf) (i v : UInt64) : Buf := b.set i.toNat v
def bpush (b : Buf) (v : UInt64) : Buf := b ++ [v]

-- ===== control: ite, Prod.casesOn, Nat.casesOn (motive at Type) =====
theorem bo_ite_t : ∀ (R : Type) (t e : R), @ite R (true = true) (instDecidableEqBool true true) t e = t :=
  fun _ _ _ => rfl
theorem bo_ite_f : ∀ (R : Type) (t e : R), @ite R (false = true) (instDecidableEqBool false true) t e = e :=
  fun _ _ _ => rfl
theorem bo_prod : ∀ (A B R : Type) (a : A) (b : B) (f : A → B → R),
    @Prod.casesOn A B (fun _ => R) (Prod.mk a b) f = f a b := fun _ _ _ _ _ _ => rfl
theorem bo_nat_z : ∀ (R : Type) (z : R) (s : Nat → R),
    @Nat.casesOn (fun _ => R) Nat.zero z s = z := fun _ _ _ => rfl
theorem bo_nat_s : ∀ (R : Type) (n : Nat) (z : R) (s : Nat → R),
    @Nat.casesOn (fun _ => R) (Nat.succ n) z s = s n := fun _ _ _ _ => rfl

-- ===== one equation per prelude op (unfolding, pointwise) =====
theorem bo_rd : ∀ (xs : List UInt8) (i : UInt64), rd xs i = (xs.getD i.toNat 0).toUInt64 := fun _ _ => rfl
theorem bo_len : ∀ xs : List UInt8, len xs = xs.length.toUInt64 := fun _ => rfl
theorem bo_put : ∀ (o : List UInt8) (b : UInt64), put o b = o ++ [b.toUInt8] := fun _ _ => rfl
theorem bo_len' : ∀ xs : List UInt8, len' xs = xs.length := fun _ => rfl
theorem bo_bnew : bnew = ([] : List UInt64) := rfl
theorem bo_bsize : ∀ b : List UInt64, bsize b = b.length.toUInt64 := fun _ => rfl
theorem bo_bget : ∀ (b : List UInt64) (i : UInt64), bget b i = b.getD i.toNat 0 := fun _ _ => rfl
theorem bo_bset : ∀ (b : List UInt64) (i v : UInt64), bset b i v = b.set i.toNat v := fun _ _ _ => rfl
theorem bo_bpush : ∀ (b : List UInt64) (v : UInt64), bpush b v = b ++ [v] := fun _ _ => rfl

-- ===== building blocks (constructor-level recursion equations) =====
-- List.length, ++, getD, set
theorem bo_length_nil : ∀ T : Type, @List.length T [] = Nat.zero := fun _ => rfl
theorem bo_length_cons : ∀ (T : Type) (a : T) (l : List T), (a :: l).length = Nat.succ l.length := fun _ _ _ => rfl
theorem bo_app_nil : ∀ (T : Type) (l : List T), [] ++ l = l := fun _ _ => rfl
theorem bo_app_cons : ∀ (T : Type) (a : T) (l m : List T), (a :: l) ++ m = a :: (l ++ m) := fun _ _ _ _ => rfl
theorem bo_getD_nil : ∀ (T : Type) (n : Nat) (d : T), ([] : List T).getD n d = d := by
  intro T n d; simp
theorem bo_getD_zero : ∀ (T : Type) (a : T) (l : List T) (d : T), (a :: l).getD Nat.zero d = a := by
  intro T a l d; simp
theorem bo_getD_succ : ∀ (T : Type) (a : T) (l : List T) (n : Nat) (d : T), (a :: l).getD (Nat.succ n) d = l.getD n d := by
  intro T a l n d; simp
theorem bo_set_nil : ∀ (T : Type) (n : Nat) (v : T), ([] : List T).set n v = [] := fun _ _ _ => rfl
theorem bo_set_zero : ∀ (T : Type) (a : T) (l : List T) (v : T), (a :: l).set Nat.zero v = v :: l := fun _ _ _ _ => rfl
theorem bo_set_succ : ∀ (T : Type) (a : T) (l : List T) (n : Nat) (v : T), (a :: l).set (Nat.succ n) v = a :: l.set n v :=
  fun _ _ _ _ _ => rfl
-- scalar conversions
theorem bo_toUInt64 : ∀ n : Nat, n.toUInt64 = UInt64.ofNat n := fun _ => rfl
theorem bo_toNat_ofNat : ∀ n : Nat, (UInt64.ofNat n).toNat = n % 18446744073709551616 := by
  intro n; exact UInt64.toNat_ofNat'
theorem bo_u8to64 : ∀ n : Nat, (UInt8.ofNat n).toUInt64 = UInt64.ofNat (n % 256) := by
  intro n; apply UInt64.toNat_inj.mp
  have := Nat.mod_lt n (show 256 > 0 by decide)
  simp [UInt8.toNat_ofNat, UInt64.toNat_ofNat]; omega
theorem bo_u64to8 : ∀ n : Nat, (UInt64.ofNat n).toUInt8 = UInt8.ofNat n := by
  intro n; apply UInt8.toNat_inj.mp; simp [UInt64.toNat_ofNat', UInt8.toNat_ofNat', Nat.mod_mod_of_dvd]
theorem bo_wrap8 : ∀ n : Nat, UInt8.ofNat (n + 256) = UInt8.ofNat n := by
  intro n; apply UInt8.toNat_inj.mp; simp [UInt8.toNat_ofNat', Nat.add_mod_right]
-- the one place a modulus appears: indices are `UInt64.ofNat k` with `k < 2^64`
theorem bo_mod_lt : ∀ n m : Nat, Nat.blt n m = true → n % m = n := fun n m h => Nat.mod_eq_of_lt (Nat.blt_eq.mp h)
theorem bo_ble_z : ∀ m : Nat, Nat.ble Nat.zero m = true := fun _ => rfl
theorem bo_ble_sz : ∀ n : Nat, Nat.ble (Nat.succ n) Nat.zero = false := fun _ => rfl
theorem bo_ble_ss : ∀ n m : Nat, Nat.ble (Nat.succ n) (Nat.succ m) = Nat.ble n m := fun _ _ => rfl
theorem bo_blt_def : ∀ n m : Nat, Nat.blt n m = Nat.ble (Nat.succ n) m := fun _ _ => rfl

set_option pp.all true
#print bo_prod
#print bo_nat_z
#print bo_nat_s
#print bo_rd
#print bo_bset
#print bo_getD_succ
#print axioms bo_getD_succ
#print axioms bo_u8to64
#print axioms bo_u64to8
#print axioms bo_wrap8
#print axioms bo_toNat_ofNat
#print axioms bo_ble_z
