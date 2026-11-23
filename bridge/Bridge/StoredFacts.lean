/- Bridge.StoredFacts: a sanity check that every stored theorem the bridge ASSUMES (`HasTy env "<name>" [] <E>`
fields of the `*Env` structures) is a TRUE Lean statement.  For each one: the original E-expression in a comment,
then `theorem <name>_holds : <the same statement in Lean syntax> := <proof>`, core Lean only (no Mathlib).

Reading key: `piN [(T1,_),…] body` = `∀ x1 : T1, …, body`; `.bvar 0` = innermost binder; `eqE u T a b` = `@Eq T a b`;
`opE f hi T I a b` = `@f T T T (@hi T I) a b`; `bin2 f a b` = `f a b`; `litNat k` = `@OfNat.ofNat Nat k (instOfNatNat k)`;
`nz`/`sc` = `Nat.zero`/`Nat.succ`; `ofN` = `UInt64.ofNat`; `of8` = `UInt8.ofNat`;
`guard a` = `Nat.blt a 18446744073709551616 = true` (`nLit = litNat UInt64.size`).
The prelude ops (`rd`, `len`, `len'`, `put`, `Buf`, `bnew`, `bsize`, `bget`, `bset`, `bpush`) are the real
definitions of `Nano/Main/Prelude.lean` (root namespace), imported below.

Notation is used where it elaborates to exactly the E-head (`+` = `@HAdd.hAdd T T T (@instHAdd T instAddT)`, etc.);
`@`-explicit forms are used for `==` (core has other `BEq` instances), `ite` (explicit decidability instance),
`OfNat.ofNat` (explicit instance), and `Nat.pow` (written as `Nat.pow`, not `^`). -/
import Nano.Main.Prelude

namespace Bridge.StoredFacts

/-! ## Add.lean (`AddEnv`) -/

-- outParam_eq : eqE 3 (.sort 2) (.app (.const "outParam" [2]) (.sort 1)) (.sort 1)
theorem outParam_eq_holds : @Eq.{3} (Type 1) (outParam.{2} Type) Type := rfl

-- add0 : piN [(tNat, true)] (eqE 1 tNat (addN (.bvar 0) (.const "Nat.zero" [])) (.bvar 0))
theorem add0_holds : ∀ n : Nat, n + Nat.zero = n := fun _ => rfl

-- addS : piN [(tNat, true), (tNat, true)] (eqE 1 tNat
--   (addN (.bvar 1) (.app (.const "Nat.succ" []) (.bvar 0))) (.app (.const "Nat.succ" []) (addN (.bvar 1) (.bvar 0))))
theorem addS_holds : ∀ n m : Nat, n + Nat.succ m = Nat.succ (n + m) := fun _ _ => rfl

-- br_add : piN [(tNat, true), (tNat, true)] (eqE 1 tU
--   (addU (ofN (.bvar 1)) (ofN (.bvar 0))) (ofN (addN (.bvar 1) (.bvar 0))))
theorem br_add_holds : ∀ a b : Nat, UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) := by
  intro a b
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod]

-- br_wrap : piN [(tNat, true)] (eqE 1 tU (ofN (addN (.bvar 0) (litNat UInt64.size))) (ofN (.bvar 0)))
theorem br_wrap_holds : ∀ n : Nat, UInt64.ofNat (n + 18446744073709551616) = UInt64.ofNat n := by
  intro n
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_ofNat']

-- br_litN : piN [(tNat, true)] (eqE 1 tNat
--   (.app (.app (.app (.const "OfNat.ofNat" [0]) tNat) (.bvar 0)) (.app (.const "instOfNatNat" []) (.bvar 0))) (.bvar 0))
theorem br_litN_holds : ∀ n : Nat, @OfNat.ofNat Nat n (instOfNatNat n) = n := fun _ => rfl

/-! ## EvMini.lean -/

-- buf_eq : eqE 2 (.sort 1) (.const "Buf" []) (.app (.const "List" [0]) tU)
theorem buf_eq_holds : @Eq.{2} Type Buf (List.{0} UInt64) := rfl

/-! ## Arith.lean (`SubEnv`, `MulEnv`) -/

-- sub_n0 : piN [(tNat, true)] (eqE 1 tNat (subN (.bvar 0) nz) (.bvar 0))
theorem sub_n0_holds : ∀ n : Nat, n - Nat.zero = n := fun _ => rfl

-- sub_ss : piN [(tNat, true), (tNat, true)] (eqE 1 tNat (subN (sc (.bvar 1)) (sc (.bvar 0))) (subN (.bvar 1) (.bvar 0)))
theorem sub_ss_holds : ∀ n m : Nat, Nat.succ n - Nat.succ m = n - m := fun n m => Nat.succ_sub_succ n m

-- sub_0s : piN [(tNat, true)] (eqE 1 tNat (subN nz (sc (.bvar 0))) nz)
theorem sub_0s_holds : ∀ n : Nat, Nat.zero - Nat.succ n = Nat.zero := fun _ => Nat.zero_sub _

-- br_sub : piN [(tNat, true), (tNat, true), (guard (.bvar 0), true)]
--   (eqE 1 tU (subU (ofN (.bvar 2)) (ofN (.bvar 1))) (ofN (addN (.bvar 2) (subN nLit (.bvar 1)))))
theorem br_sub_holds : ∀ a b : Nat, Nat.blt b 18446744073709551616 = true →
    UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a + (18446744073709551616 - b)) := by
  intro a b hb
  have hb' : b < 18446744073709551616 := Nat.blt_eq.mp hb
  apply UInt64.toNat_inj.mp
  have h64 : (2:Nat) ^ 64 = 18446744073709551616 := rfl
  simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', h64, Nat.mod_eq_of_lt hb']
  omega

-- mul_n0 : piN [(tNat, true)] (eqE 1 tNat (mulN (.bvar 0) nz) nz)
theorem mul_n0_holds : ∀ n : Nat, n * Nat.zero = Nat.zero := fun _ => rfl

-- mul_ns : piN [(tNat, true), (tNat, true)] (eqE 1 tNat (mulN (.bvar 1) (sc (.bvar 0))) (addN (mulN (.bvar 1) (.bvar 0)) (.bvar 1)))
theorem mul_ns_holds : ∀ n m : Nat, n * Nat.succ m = n * m + n := fun _ _ => rfl

-- br_mul : piN [(tNat, true), (tNat, true)] (eqE 1 tU (mulU (ofN (.bvar 1)) (ofN (.bvar 0))) (ofN (mulN (.bvar 1) (.bvar 0))))
theorem br_mul_holds : ∀ a b : Nat, UInt64.ofNat a * UInt64.ofNat b = UInt64.ofNat (a * b) := by
  intro a b
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_mul, UInt64.toNat_ofNat', Nat.mul_mod]

/-! ## Cmp.lean (`CmpEnv`, `BeqEnv`) -/

-- ble0 : piN [(tNat, true)] (eqE 1 tB (bin2 "Nat.ble" nz (.bvar 0)) tt)
theorem ble0_holds : ∀ n : Nat, Nat.ble Nat.zero n = true := fun n => by cases n <;> rfl

-- bleS0 : piN [(tNat, true)] (eqE 1 tB (bin2 "Nat.ble" (sc (.bvar 0)) nz) ff)
theorem bleS0_holds : ∀ n : Nat, Nat.ble (Nat.succ n) Nat.zero = false := fun _ => rfl

-- bleSS : piN [(tNat, true), (tNat, true)] (eqE 1 tB (bin2 "Nat.ble" (sc (.bvar 1)) (sc (.bvar 0))) (bin2 "Nat.ble" (.bvar 1) (.bvar 0)))
theorem bleSS_holds : ∀ n m : Nat, Nat.ble (Nat.succ n) (Nat.succ m) = Nat.ble n m := fun _ _ => rfl

-- beq00 : eqE 1 tB (bin2 "Nat.beq" nz nz) tt
theorem beq00_holds : Nat.beq Nat.zero Nat.zero = true := rfl

-- beq0S : piN [(tNat, true)] (eqE 1 tB (bin2 "Nat.beq" nz (sc (.bvar 0))) ff)
theorem beq0S_holds : ∀ n : Nat, Nat.beq Nat.zero (Nat.succ n) = false := fun _ => rfl

-- beqS0 : piN [(tNat, true)] (eqE 1 tB (bin2 "Nat.beq" (sc (.bvar 0)) nz) ff)
theorem beqS0_holds : ∀ n : Nat, Nat.beq (Nat.succ n) Nat.zero = false := fun _ => rfl

-- beqSS : piN [(tNat, true), (tNat, true)] (eqE 1 tB (bin2 "Nat.beq" (sc (.bvar 1)) (sc (.bvar 0))) (bin2 "Nat.beq" (.bvar 1) (.bvar 0)))
theorem beqSS_holds : ∀ n m : Nat, Nat.beq (Nat.succ n) (Nat.succ m) = Nat.beq n m := fun _ _ => rfl

-- bltDef : piN [(tNat, true), (tNat, true)] (eqE 1 tB (bin2 "Nat.blt" (.bvar 1) (.bvar 0)) (bin2 "Nat.ble" (sc (.bvar 1)) (.bvar 0)))
theorem bltDef_holds : ∀ n m : Nat, Nat.blt n m = Nat.ble (Nat.succ n) m := fun _ _ => rfl

-- br_beq : piN [(tNat, true), (tNat, true), (guard (.bvar 1), true), (guard (.bvar 1), true)]
--   (eqE 1 tB (beqU (ofN (.bvar 3)) (ofN (.bvar 2))) (bin2 "Nat.beq" (.bvar 3) (.bvar 2)))
-- beqU a b = @BEq.beq UInt64 (@instBEqOfDecidableEq UInt64 instDecidableEqUInt64) a b
theorem br_beq_holds : ∀ a b : Nat, Nat.blt a 18446744073709551616 = true → Nat.blt b 18446744073709551616 = true →
    @BEq.beq UInt64 (@instBEqOfDecidableEq UInt64 instDecidableEqUInt64) (UInt64.ofNat a) (UInt64.ofNat b)
      = Nat.beq a b := by
  intro a b ha hb
  have ha' : a < 18446744073709551616 := Nat.blt_eq.mp ha
  have hb' : b < 18446744073709551616 := Nat.blt_eq.mp hb
  show decide (UInt64.ofNat a = UInt64.ofNat b) = Nat.beq a b
  have : (UInt64.ofNat a = UInt64.ofNat b) ↔ a = b := by
    rw [← UInt64.toNat_inj]
    simp only [UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by simpa using ha'), Nat.mod_eq_of_lt (by simpa using hb')]
  cases h : Nat.beq a b
  · have hne : a ≠ b := by intro e; subst e; simp [Nat.beq_refl] at h
    simpa [this] using hne
  · simpa [this] using Nat.eq_of_beq_eq_true h

/-! ## Ite.lean (`IteEnv`) -/

-- deqB : eqE 2 (.sort 1) (.app (.const "DecidableEq" [1]) tB)
--   (.forallE tB (.forallE tB (.app (.const "Decidable" []) (eqB (.bvar 1) (.bvar 0))) false) false)
theorem deqB_holds : @Eq.{2} Type (DecidableEq.{1} Bool) (∀ a b : Bool, Decidable (@Eq Bool a b)) := rfl

-- ite_t : piN [(.sort 1, true), (.bvar 0, true), (.bvar 1, true)]
--   (eqE 1 (.bvar 2) (iteE (.bvar 2) (eqB tt tt) (decB tt tt) (.bvar 1) (.bvar 0)) (.bvar 1))
theorem ite_t_holds : ∀ (R : Type) (t e : R),
    @ite R (@Eq Bool true true) (instDecidableEqBool true true) t e = t := fun _ _ _ => rfl

-- ite_f : piN [(.sort 1, true), (.bvar 0, true), (.bvar 1, true)]
--   (eqE 1 (.bvar 2) (iteE (.bvar 2) (eqB ff tt) (decB ff tt) (.bvar 1) (.bvar 0)) (.bvar 0))
theorem ite_f_holds : ∀ (R : Type) (t e : R),
    @ite R (@Eq Bool false true) (instDecidableEqBool false true) t e = e := fun _ _ _ => rfl

/-! ## IteLt.lean (`LtEnv`)
`iteLtTy res v = piN [(.sort 1), (tNat), (tNat), (.bvar 2), (.bvar 3), (guard (.bvar 3)), (guard (.bvar 3)),
  (bltG (.bvar 5) (.bvar 4) v)] (eqE 1 (.bvar 7) (iteE (.bvar 7) (ltU (ofN (.bvar 6)) (ofN (.bvar 5)))
  (decLtU (ofN (.bvar 6)) (ofN (.bvar 5))) (.bvar 4) (.bvar 3)) res)`, i.e. binders R a b t e ha hb h. -/

theorem ite_lt_aux (a b : Nat) (ha : Nat.blt a 18446744073709551616 = true)
    (hb : Nat.blt b 18446744073709551616 = true) : UInt64.ofNat a < UInt64.ofNat b ↔ Nat.blt a b = true := by
  have ha' : a < 18446744073709551616 := Nat.blt_eq.mp ha
  have hb' : b < 18446744073709551616 := Nat.blt_eq.mp hb
  rw [Nat.blt_eq, UInt64.lt_iff_toNat_lt]
  simp only [UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by simpa using ha'), Nat.mod_eq_of_lt (by simpa using hb')]

-- ite_lt_t : iteLtTy (.bvar 4) tt
theorem ite_lt_t_holds : ∀ (R : Type) (a b : Nat) (t e : R), Nat.blt a 18446744073709551616 = true →
    Nat.blt b 18446744073709551616 = true → Nat.blt a b = true →
    @ite R (@LT.lt UInt64 instLTUInt64 (UInt64.ofNat a) (UInt64.ofNat b))
      (UInt64.decLt (UInt64.ofNat a) (UInt64.ofNat b)) t e = t := by
  intro R a b t e ha hb h
  simp [(ite_lt_aux a b ha hb).mpr h]

-- ite_lt_f : iteLtTy (.bvar 3) ff
theorem ite_lt_f_holds : ∀ (R : Type) (a b : Nat) (t e : R), Nat.blt a 18446744073709551616 = true →
    Nat.blt b 18446744073709551616 = true → Nat.blt a b = false →
    @ite R (@LT.lt UInt64 instLTUInt64 (UInt64.ofNat a) (UInt64.ofNat b))
      (UInt64.decLt (UInt64.ofNat a) (UInt64.ofNat b)) t e = e := by
  intro R a b t e ha hb h
  have hn : ¬ UInt64.ofNat a < UInt64.ofNat b := fun hl => by rw [(ite_lt_aux a b ha hb).mp hl] at h; cases h
  simp [hn]

/-! ## IteNat.lean (`NatEqEnv`) -/

-- br_nbeq : piN [(tNat, true), (tNat, true)] (eqE 1 tB (beqN (.bvar 1) (.bvar 0)) (bin2 "Nat.beq" (.bvar 1) (.bvar 0)))
-- beqN a b = @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b
theorem br_nbeq_holds : ∀ a b : Nat,
    @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b = Nat.beq a b := by
  intro a b
  show decide (a = b) = Nat.beq a b
  cases h : Nat.beq a b
  · have hne : a ≠ b := by intro e; subst e; simp [Nat.beq_refl] at h
    simpa using hne
  · simpa using Nat.eq_of_beq_eq_true h

/-! ## Shift.lean (`ShiftEnv`) -/

-- pow_z : piN [(tNat, true)] (eqE 1 tNat (powE (.bvar 0) nz) (sc nz))
theorem pow_z_holds : ∀ n : Nat, Nat.pow n Nat.zero = Nat.succ Nat.zero := fun _ => rfl

-- pow_s : piN [(tNat, true), (tNat, true)] (eqE 1 tNat (powE (.bvar 1) (sc (.bvar 0))) (mulN (powE (.bvar 1) (.bvar 0)) (.bvar 1)))
theorem pow_s_holds : ∀ n m : Nat, Nat.pow n (Nat.succ m) = Nat.pow n m * n := fun _ _ => rfl

-- mod_char : piN [(tNat, true), (tNat, true), (tNat, true), (eqE 1 tB (bin2 "Nat.blt" (.bvar 1) (.bvar 0)) tt, true)]
--   (eqE 1 tNat (modN (addN (mulN (.bvar 3) (.bvar 1)) (.bvar 2)) (.bvar 1)) (.bvar 2))
theorem mod_char_holds : ∀ q r d : Nat, Nat.blt r d = true → (q * d + r) % d = r := by
  intro q r d h
  have h' : r < d := Nat.blt_eq.mp h
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h']

-- div_char : piN [(tNat, true), (tNat, true), (tNat, true), (eqE 1 tB (bin2 "Nat.blt" (.bvar 1) (.bvar 0)) tt, true)]
--   (eqE 1 tNat (divN (addN (mulN (.bvar 3) (.bvar 1)) (.bvar 2)) (.bvar 1)) (.bvar 3))
theorem div_char_holds : ∀ q r d : Nat, Nat.blt r d = true → (q * d + r) / d = q := by
  intro q r d h
  have h' : r < d := Nat.blt_eq.mp h
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le r) h'
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt h', Nat.zero_add]

-- br_shl : piN [(tNat, true), (tNat, true)]
--   (eqE 1 tU (shlU (ofN (.bvar 1)) (ofN (.bvar 0))) (ofN (mulN (.bvar 1) (powE (litNat 2) (modN (.bvar 0) (litNat 64))))))
theorem br_shl_holds : ∀ a b : Nat,
    UInt64.ofNat a <<< UInt64.ofNat b = UInt64.ofNat (a * Nat.pow 2 (b % 64)) := by
  intro a b
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', Nat.shiftLeft_eq]
  show a % 2 ^ 64 * 2 ^ (b % 2 ^ 64 % 64) % 2 ^ 64 = a * 2 ^ (b % 64) % 2 ^ 64
  rw [Nat.mod_mod_of_dvd b (by decide : 64 ∣ 2 ^ 64), Nat.mod_mul_mod]

-- br_shr : piN [(tNat, true), (tNat, true), (guard (.bvar 1), true)]
--   (eqE 1 tU (shrU (ofN (.bvar 2)) (ofN (.bvar 1))) (ofN (divN (.bvar 2) (powE (litNat 2) (modN (.bvar 1) (litNat 64))))))
theorem br_shr_holds : ∀ a b : Nat, Nat.blt a 18446744073709551616 = true →
    UInt64.ofNat a >>> UInt64.ofNat b = UInt64.ofNat (a / Nat.pow 2 (b % 64)) := by
  intro a b ha
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  have ha' : a < 2 ^ 64 := Nat.blt_eq.mp ha
  show a % 2 ^ 64 / 2 ^ (b % 2 ^ 64 % 64) = a / 2 ^ (b % 64) % 2 ^ 64
  rw [Nat.mod_mod_of_dvd b (by decide : 64 ∣ 2 ^ 64), Nat.mod_eq_of_lt ha',
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha')]

/-! ## Bits.lean (`BitsEnv`)
`recTy f low = piN [(tNat), (tNat)] (eqE 1 tNat (bin2 f (.bvar 1) (.bvar 0))
  (addN (mulN two (bin2 f (divN (.bvar 1) two) (divN (.bvar 0) two))) (low (modN (.bvar 1) two) (modN (.bvar 0) two))))` -/

-- land_z : piN [(tNat, true)] (eqE 1 tNat (bin2 "Nat.land" nz (.bvar 0)) nz)
theorem land_z_holds : ∀ n : Nat, Nat.land Nat.zero n = Nat.zero := fun n => Nat.zero_and n

-- lor_z : piN [(tNat, true)] (eqE 1 tNat (bin2 "Nat.lor" nz (.bvar 0)) (.bvar 0))
theorem lor_z_holds : ∀ n : Nat, Nat.lor Nat.zero n = n := fun n => Nat.zero_or n

-- land_r : recTy "Nat.land" mulN
theorem land_r_holds : ∀ a b : Nat,
    Nat.land a b = 2 * Nat.land (a / 2) (b / 2) + a % 2 * (b % 2) := by
  intro a b
  show Nat.bitwise and a b = 2 * Nat.bitwise and (a / 2) (b / 2) + a % 2 * (b % 2)
  by_cases ha : a = 0
  · subst ha; simp [Nat.bitwise]
  by_cases hb : b = 0
  · subst hb; simp [Nat.bitwise]
  conv => lhs; unfold Nat.bitwise
  simp only [ha, hb, ↓reduceIte]
  rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;> rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;>
    simp [h1, h2] <;> omega

-- lor_r : recTy "Nat.lor" fun x y => modN (addN (addN x y) (mulN x y)) two
theorem lor_r_holds : ∀ a b : Nat,
    Nat.lor a b = 2 * Nat.lor (a / 2) (b / 2) + (a % 2 + b % 2 + a % 2 * (b % 2)) % 2 := by
  intro a b
  show Nat.bitwise or a b = 2 * Nat.bitwise or (a / 2) (b / 2) + (a % 2 + b % 2 + a % 2 * (b % 2)) % 2
  by_cases ha : a = 0
  · subst ha
    have hz : ∀ x, Nat.bitwise or 0 x = x := fun x => Nat.zero_or x
    rw [Nat.zero_div, hz, hz]; omega
  by_cases hb : b = 0
  · subst hb
    have hz : ∀ x, Nat.bitwise or x 0 = x := fun x => Nat.or_zero x
    rw [Nat.zero_div, hz, hz]; omega
  conv => lhs; unfold Nat.bitwise
  simp only [ha, hb, ↓reduceIte]
  rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;> rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;>
    simp [h1, h2] <;> omega

-- br_and : piN [(tNat, true), (tNat, true)] (eqE 1 tU (andU (ofN (.bvar 1)) (ofN (.bvar 0))) (ofN (bin2 "Nat.land" (.bvar 1) (.bvar 0))))
theorem br_and_holds : ∀ a b : Nat, UInt64.ofNat a &&& UInt64.ofNat b = UInt64.ofNat (Nat.land a b) := by
  intro a b
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_and, UInt64.toNat_ofNat']
  exact Nat.and_mod_two_pow.symm

-- br_or : piN [(tNat, true), (tNat, true)] (eqE 1 tU (orU (ofN (.bvar 1)) (ofN (.bvar 0))) (ofN (bin2 "Nat.lor" (.bvar 1) (.bvar 0))))
theorem br_or_holds : ∀ a b : Nat, UInt64.ofNat a ||| UInt64.ofNat b = UInt64.ofNat (Nat.lor a b) := by
  intro a b
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_or, UInt64.toNat_ofNat']
  exact Nat.or_mod_two_pow.symm

/-! ## Iota.lean (`IotaEnv`), Iota2.lean (`ProdCEnv`)
`motive i = .lam tNat (.bvar (i + 1))`, i.e. `fun _ : Nat => R`. -/

-- nat_z : piN [(.sort 1, true), (.bvar 0, true), (.forallE tNat (.bvar 2) false, true)]
--   (eqE 1 (.bvar 2) (.app (.app (.app (.app (.const "Nat.casesOn" [1]) (motive 2)) (.const "Nat.zero" [])) (.bvar 1)) (.bvar 0)) (.bvar 1))
theorem nat_z_holds : ∀ (R : Type) (z : R) (s : Nat → R),
    @Nat.casesOn.{1} (fun _ : Nat => R) Nat.zero z s = z := fun _ _ _ => rfl

-- nat_s : piN [(.sort 1, true), (.bvar 0, true), (.forallE tNat (.bvar 2) false, true), (tNat, true)]
--   (eqE 1 (.bvar 3) (.app (.app (.app (.app (.const "Nat.casesOn" [1]) (motive 3))
--     (.app (.const "Nat.succ" []) (.bvar 0))) (.bvar 2)) (.bvar 1)) (.app (.bvar 1) (.bvar 0)))
theorem nat_s_holds : ∀ (R : Type) (z : R) (s : Nat → R) (n : Nat),
    @Nat.casesOn.{1} (fun _ : Nat => R) (Nat.succ n) z s = s n := fun _ _ _ _ => rfl

-- prod_c : piN [(.sort 1, true), (.sort 1, true), (.sort 1, true),
--     (.forallE (.bvar 2) (.forallE (.bvar 2) (.bvar 2) false) false, true), (.bvar 3, true), (.bvar 3, true)]
--   (eqE 1 (.bvar 3)
--     (.app (.app (.app (.app (.app (.const "Prod.casesOn" [1, 0, 0]) (.bvar 5)) (.bvar 4))
--         (.lam (.app (.app (.const "Prod" [0, 0]) (.bvar 5)) (.bvar 4)) (.bvar 4) false))
--       (.app (.app (.app (.app (.const "Prod.mk" [0, 0]) (.bvar 5)) (.bvar 4)) (.bvar 1)) (.bvar 0))) (.bvar 2))
--     (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))
theorem prod_c_holds : ∀ (A B R : Type) (f : A → B → R) (a : A) (b : B),
    @Prod.casesOn.{1, 0, 0} A B (fun _ : Prod A B => R) (@Prod.mk A B a b) f = f a b := fun _ _ _ _ _ _ => rfl

/-! ## Len.lean (`LenEnv`) -/

-- len_nil : piN [(.sort 1, true)] (eqE 1 tNat (lenE (.bvar 0) (.app (.const "List.nil" [0]) (.bvar 0))) (.const "Nat.zero" []))
theorem len_nil_holds : ∀ T : Type, @List.length T (@List.nil T) = Nat.zero := fun _ => rfl

-- len_cons : piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true)]
--   (eqE 1 tNat (lenE (.bvar 2) (.app (.app (.app (.const "List.cons" [0]) (.bvar 2)) (.bvar 1)) (.bvar 0)))
--     (.app (.const "Nat.succ" []) (lenE (.bvar 2) (.bvar 0))))
theorem len_cons_holds : ∀ (T : Type) (a : T) (l : List T),
    @List.length T (@List.cons T a l) = Nat.succ (@List.length T l) := fun _ _ _ => rfl

-- toU : piN [(tNat, true)] (eqE 1 tU (.app (.const "Nat.toUInt64" []) (.bvar 0)) (ofN (.bvar 0)))
theorem toU_holds : ∀ n : Nat, Nat.toUInt64 n = UInt64.ofNat n := fun _ => rfl

-- bo_len' : piN [(tList tU8, true)] (eqE 1 tNat (.app (.const "len'" []) (.bvar 0)) (lenE tU8 (.bvar 0)))
theorem bo_len'_holds : ∀ x : List UInt8, len' x = @List.length UInt8 x := fun _ => rfl

-- bo_len : piN [(tList tU8, true)] (eqE 1 tU (.app (.const "len" []) (.bvar 0))
--   (.app (.const "Nat.toUInt64" []) (lenE tU8 (.bvar 0))))
theorem bo_len_holds : ∀ x : List UInt8, len x = Nat.toUInt64 (@List.length UInt8 x) := fun _ => rfl

-- bo_bsize : piN [(tList tU, true)] (eqE 1 tU (.app (.const "bsize" []) (.bvar 0))
--   (.app (.const "Nat.toUInt64" []) (lenE tU (.bvar 0))))
theorem bo_bsize_holds : ∀ b : List UInt64, bsize b = Nat.toUInt64 (@List.length UInt64 b) := fun _ => rfl

/-! ## Push.lean (`PushEnv`) -/

-- app_nil : piN [(.sort 1, true), (tList (.bvar 0), true)] (eqE 1 (tList (.bvar 1)) (appE (.bvar 1) (nilE (.bvar 1)) (.bvar 0)) (.bvar 0))
theorem app_nil_holds : ∀ (T : Type) (l : List T), @List.append T (@List.nil T) l = l := fun _ _ => rfl

-- app_cons : piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true), (tList (.bvar 2), true)]
--   (eqE 1 (tList (.bvar 3)) (appE (.bvar 3) (consE (.bvar 3) (.bvar 2) (.bvar 1)) (.bvar 0))
--     (consE (.bvar 3) (.bvar 2) (appE (.bvar 3) (.bvar 1) (.bvar 0))))
theorem app_cons_holds : ∀ (T : Type) (a : T) (l m : List T),
    @List.append T (@List.cons T a l) m = @List.cons T a (@List.append T l m) := fun _ _ _ _ => rfl

-- bo_bnew : eqE 1 (tList tU) (.const "bnew" []) (nilE tU)
theorem bo_bnew_holds : bnew = @List.nil UInt64 := rfl

-- bo_bpush : piN [(tList tU, true), (tU, true)]
--   (eqE 1 (tList tU) (.app (.app (.const "bpush" []) (.bvar 1)) (.bvar 0)) (appE tU (.bvar 1) (consE tU (.bvar 0) (nilE tU))))
theorem bo_bpush_holds : ∀ (b : List UInt64) (v : UInt64),
    bpush b v = @List.append UInt64 b (@List.cons UInt64 v (@List.nil UInt64)) := fun _ _ => rfl

/-! ## Index.lean (`IdxEnv`) -/

-- toNat_ofNat : piN [(tNat, true), (guard (.bvar 0), true)] (eqE 1 tNat (toNatE (ofN (.bvar 1))) (.bvar 1))
theorem toNat_ofNat_holds : ∀ n : Nat, Nat.blt n 18446744073709551616 = true → UInt64.toNat (UInt64.ofNat n) = n := by
  intro n h
  have h' : n < 18446744073709551616 := Nat.blt_eq.mp h
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa using h')]

-- getD_nil : piN [(.sort 1, true), (tNat, true), (.bvar 1, true)]
--   (eqE 1 (.bvar 2) (getDE (.bvar 2) (nilE (.bvar 2)) (.bvar 1) (.bvar 0)) (.bvar 0))
theorem getD_nil_holds : ∀ (T : Type) (i : Nat) (d : T), @List.getD T (@List.nil T) i d = d := fun _ _ _ => rfl

-- getD_cz : piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true), (.bvar 2, true)]
--   (eqE 1 (.bvar 3) (getDE (.bvar 3) (consE (.bvar 3) (.bvar 2) (.bvar 1)) nz (.bvar 0)) (.bvar 2))
theorem getD_cz_holds : ∀ (T : Type) (a : T) (l : List T) (d : T),
    @List.getD T (@List.cons T a l) Nat.zero d = a := fun _ _ _ _ => rfl

-- getD_cs : piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true), (tNat, true), (.bvar 3, true)]
--   (eqE 1 (.bvar 4) (getDE (.bvar 4) (consE (.bvar 4) (.bvar 3) (.bvar 2)) (sc (.bvar 1)) (.bvar 0))
--     (getDE (.bvar 4) (.bvar 2) (.bvar 1) (.bvar 0)))
theorem getD_cs_holds : ∀ (T : Type) (a : T) (l : List T) (i : Nat) (d : T),
    @List.getD T (@List.cons T a l) (Nat.succ i) d = @List.getD T l i d := fun _ _ _ _ _ => rfl

-- set_nil : piN [(.sort 1, true), (tNat, true), (.bvar 1, true)]
--   (eqE 1 (tList (.bvar 2)) (setE (.bvar 2) (nilE (.bvar 2)) (.bvar 1) (.bvar 0)) (nilE (.bvar 2)))
theorem set_nil_holds : ∀ (T : Type) (i : Nat) (v : T), @List.set T (@List.nil T) i v = @List.nil T :=
  fun _ _ _ => rfl

-- set_cz : piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true), (.bvar 2, true)]
--   (eqE 1 (tList (.bvar 3)) (setE (.bvar 3) (consE (.bvar 3) (.bvar 2) (.bvar 1)) nz (.bvar 0))
--     (consE (.bvar 3) (.bvar 0) (.bvar 1)))
theorem set_cz_holds : ∀ (T : Type) (a : T) (l : List T) (v : T),
    @List.set T (@List.cons T a l) Nat.zero v = @List.cons T v l := fun _ _ _ _ => rfl

-- set_cs : piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true), (tNat, true), (.bvar 3, true)]
--   (eqE 1 (tList (.bvar 4)) (setE (.bvar 4) (consE (.bvar 4) (.bvar 3) (.bvar 2)) (sc (.bvar 1)) (.bvar 0))
--     (consE (.bvar 4) (.bvar 3) (setE (.bvar 4) (.bvar 2) (.bvar 1) (.bvar 0))))
theorem set_cs_holds : ∀ (T : Type) (a : T) (l : List T) (i : Nat) (v : T),
    @List.set T (@List.cons T a l) (Nat.succ i) v = @List.cons T a (@List.set T l i v) := fun _ _ _ _ _ => rfl

-- bo_bget : piN [(tList tU, true), (tU, true)]
--   (eqE 1 tU (.app (.app (.const "bget" []) (.bvar 1)) (.bvar 0)) (getDE tU (.bvar 1) (toNatE (.bvar 0)) lit0))
-- lit0 = @OfNat.ofNat UInt64 0 (@UInt64.instOfNat 0)
theorem bo_bget_holds : ∀ (b : List UInt64) (i : UInt64),
    bget b i = @List.getD UInt64 b (UInt64.toNat i) (@OfNat.ofNat UInt64 0 (@UInt64.instOfNat 0)) := fun _ _ => rfl

-- bo_bset : piN [(tList tU, true), (tU, true), (tU, true)]
--   (eqE 1 (tList tU) (.app (.app (.app (.const "bset" []) (.bvar 2)) (.bvar 1)) (.bvar 0)) (setE tU (.bvar 2) (toNatE (.bvar 1)) (.bvar 0)))
theorem bo_bset_holds : ∀ (b : List UInt64) (i v : UInt64),
    bset b i v = @List.set UInt64 b (UInt64.toNat i) v := fun _ _ _ => rfl

/-! ## Bytes.lean (`ByteEnv`) -/

-- bo_put : piN [(tList tU8, true), (tU, true)]
--   (eqE 1 (tList tU8) (.app (.app (.const "put" []) (.bvar 1)) (.bvar 0))
--     (appE tU8 (.bvar 1) (consE tU8 (.app (.const "UInt64.toUInt8" []) (.bvar 0)) (nilE tU8))))
theorem bo_put_holds : ∀ (o : List UInt8) (b : UInt64),
    put o b = @List.append UInt8 o (@List.cons UInt8 (UInt64.toUInt8 b) (@List.nil UInt8)) := fun _ _ => rfl

-- bo_u64to8 : piN [(tNat, true)] (eqE 1 tU8 (.app (.const "UInt64.toUInt8" []) (ofN (.bvar 0))) (of8 (.bvar 0)))
theorem bo_u64to8_holds : ∀ n : Nat, UInt64.toUInt8 (UInt64.ofNat n) = UInt8.ofNat n := by
  intro n
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_ofNat']

-- bo_wrap8 : piN [(tNat, true)] (eqE 1 tU8 (of8 (addN (.bvar 0) (litNat 256))) (of8 (.bvar 0)))
theorem bo_wrap8_holds : ∀ n : Nat, UInt8.ofNat (n + 256) = UInt8.ofNat n := by
  intro n
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_ofNat']

-- bo_rd : piN [(tList tU8, true), (tU, true)]
--   (eqE 1 tU (.app (.app (.const "rd" []) (.bvar 1)) (.bvar 0))
--     (.app (.const "UInt8.toUInt64" []) (getDE tU8 (.bvar 1) (toNatE (.bvar 0)) (lit8 0))))
-- lit8 0 = @OfNat.ofNat UInt8 0 (@UInt8.instOfNat 0)
theorem bo_rd_holds : ∀ (x : List UInt8) (i : UInt64),
    rd x i = UInt8.toUInt64 (@List.getD UInt8 x (UInt64.toNat i) (@OfNat.ofNat UInt8 0 (@UInt8.instOfNat 0))) :=
  fun _ _ => rfl

-- br_lit8 : piN [(tNat, true)] (eqE 1 tU8
--   (.app (.app (.app (.const "OfNat.ofNat" [0]) tU8) (.bvar 0)) (.app (.const "UInt8.instOfNat" []) (.bvar 0))) (of8 (.bvar 0)))
theorem br_lit8_holds : ∀ n : Nat, @OfNat.ofNat UInt8 n (@UInt8.instOfNat n) = UInt8.ofNat n := fun _ => rfl

-- u8to64 : piN [(tNat, true), (eqE 1 tB (bin2 "Nat.blt" (.bvar 0) (litNat 256)) tt, true)]
--   (eqE 1 tU (.app (.const "UInt8.toUInt64" []) (of8 (.bvar 1))) (ofN (.bvar 1)))
theorem u8to64_holds : ∀ n : Nat, Nat.blt n 256 = true → UInt8.toUInt64 (UInt8.ofNat n) = UInt64.ofNat n := by
  intro n h
  have h' : n < 256 := Nat.blt_eq.mp h
  apply UInt64.toNat_inj.mp
  simp [UInt8.toNat_toUInt64, UInt64.toNat_ofNat', UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt h', Nat.mod_eq_of_lt (by omega)]

end Bridge.StoredFacts
