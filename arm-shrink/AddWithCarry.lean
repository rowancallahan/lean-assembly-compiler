import Armv9.V8Base
open Sail
namespace Armv9.Functions
theorem AddWithCarry_result {k_N : Nat} (x y : BitVec k_N) (c : BitVec 1) (h : 0 < k_N) :
    (AddWithCarry x y c).1 = x + y + c.zeroExtend k_N := by
  unfold AddWithCarry
  apply BitVec.eq_of_toNat_eq
  have e : ((k_N : Int) - 1 - 0 + 1).toNat = k_N := by omega
  simp [integer_subrange, Sail.BitVec.length, get_slice_int]
  have h1 : (((x.toNat + y.toNat + c.toNat : Nat) : Int) % 2^(k_N+1)).toNat = (x.toNat+y.toNat+c.toNat) % 2^(k_N+1) := by norm_cast
  have e2 : k_N - 1 + 1 = k_N := by omega
  rw [e2]; push_cast at h1; rw [h1]
  simp [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_succ k_N))]
#print axioms AddWithCarry_result
