/- NZCV after `subs`: the model's AddWithCarry flag vector in readable form. -/
import Arm.Base
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 100000
namespace ArmProof



/-- the flag vector `AddWithCarry` computes, as a function of its result `r` (same text as the model) -/
def awcFlags {k_N : Nat} (x y : BitVec k_N) (carry_in : BitVec 1) (result : BitVec k_N) : BitVec 4 :=
  let unsigned_sum := (((BitVec.toNat x) +i (BitVec.toNat y)) +i (BitVec.toNat carry_in))
  let signed_sum := (((BitVec.toInt x) +i (BitVec.toInt y)) +i (BitVec.toNat carry_in))
  let n : (BitVec 1) := (BitVec.join1 [(BitVec.access result ((Sail.BitVec.length y) -i 1))])
  let z : (BitVec 1) := if ((IsZero result) : Bool) then 1#1 else 0#1
  let c : (BitVec 1) := if (((BitVec.toNat result) == unsigned_sum) : Bool) then 0#1 else 1#1
  let v : (BitVec 1) := if (((BitVec.toInt result) == signed_sum) : Bool) then 0#1 else 1#1
  (((n +++ z) +++ c) +++ v)

theorem awc_flags {k_N : Nat} (x y : BitVec k_N) (c : BitVec 1) :
    (AddWithCarry x y c).2 = awcFlags x y c (AddWithCarry x y c).1 := rfl

theorem ite_bit (P : Prop) [Decidable P] : (if P then 1#1 else 0#1) = BitVec.ofBool (decide P) := by
  by_cases h : P <;> simp [h]
theorem ite_bit' (P : Prop) [Decidable P] : (if P then 0#1 else 1#1) = BitVec.ofBool (!decide P) := by
  by_cases h : P <;> simp [h]
theorem join1_ofBool (b : Bool) : BitVec.join1 [BitVec.ofBool b] = BitVec.ofBool b := by
  cases b <;> rfl
theorem bits4 (a b c d : Bool) :
    BitVec.extractLsb 3 3 (BitVec.ofBool a ++ BitVec.ofBool b ++ BitVec.ofBool c ++ BitVec.ofBool d) = BitVec.ofBool a ∧
    BitVec.extractLsb 2 2 (BitVec.ofBool a ++ BitVec.ofBool b ++ BitVec.ofBool c ++ BitVec.ofBool d) = BitVec.ofBool b ∧
    BitVec.extractLsb 1 1 (BitVec.ofBool a ++ BitVec.ofBool b ++ BitVec.ofBool c ++ BitVec.ofBool d) = BitVec.ofBool c ∧
    BitVec.extractLsb 0 0 (BitVec.ofBool a ++ BitVec.ofBool b ++ BitVec.ofBool c ++ BitVec.ofBool d) = BitVec.ofBool d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem sub_flags (x y : BitVec 64) (p : ProcState) :
    setFlags p (AddWithCarry x (~~~y) 1#1).2 = { p with N := .ofBool (x - y).msb, Z := .ofBool (x - y = 0), C := .ofBool (y.toNat ≤ x.toNat), V := .ofBool ((x - y).toInt ≠ x.toInt - y.toInt) } := by
  rw [awc_flags, AddWithCarry_64_sub]
  simp only [setFlags, awcFlags, IsZero, Sail.BitVec.extractLsb, Sail.BitVec.length, Sail.BitVec.access, ite_bit, ite_bit',
    join1_ofBool, bits4, beq_iff_eq, BitVec.msb]
  congr 1
  · congr 1
    have hx := x.isLt; have hy := y.isLt
    simp [BitVec.toNat_sub, BitVec.toNat_not]
    by_cases h : y.toNat ≤ x.toNat <;> simp [h] <;> omega
  · congr 1
    have hy := y.isLt
    rw [show (~~~y).toInt = -y.toInt - 1 by
      rw [BitVec.toInt_not, BitVec.toInt_eq_toNat_bmod]; simp only [Int.bmod]; split <;> split <;> omega]
    simp; omega
end ArmProof
