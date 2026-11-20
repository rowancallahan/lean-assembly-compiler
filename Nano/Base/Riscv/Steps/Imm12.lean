/- 12-bit immediates of any slot offset (`< 2048`), sign-extended to 64 bits. -/

namespace Proven

theorem sx12_pos (k : Nat) (h : k < 2048) : (BitVec.ofNat 12 k).signExtend 64 = BitVec.ofNat 64 k := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega

theorem sx12_neg (k : Nat) (h0 : 0 < k) (h : k ≤ 2048) :
    (-(BitVec.ofNat 12 k)).signExtend 64 = -(BitVec.ofNat 64 k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_neg, BitVec.toNat_ofNat]
  have e1 : (2 ^ 12 - k % 2 ^ 12) % 2 ^ 12 = 4096 - k := by omega
  simp only [e1]
  rw [if_pos (by simp; omega)]
  omega

end Proven
