namespace Proven.Apc
theorem beq_dec (a b : BitVec 64) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]
theorem add_res (x y : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 65 y + BitVec.setWidth 65 x) = x + y := by bv_omega
theorem sub_res (x y : BitVec 64) :
    BitVec.setWidth 64 (1#65 + (BitVec.setWidth 65 (~~~y) + BitVec.setWidth 65 x)) = x - y := by bv_omega
theorem sub_c (x y : BitVec 64) :
    (1#65 + (BitVec.setWidth 65 (~~~y) + BitVec.setWidth 65 x)).msb = decide (y.toNat ≤ x.toNat) := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.msb_eq_decide, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_not, BitVec.toNat_ofNat]
  by_cases h : y.toNat ≤ x.toNat <;> simp [h] <;> omega
theorem not65 (t : BitVec 65) : (~~~t).toInt = -t.toInt - 1 := by
  have := t.isLt
  rw [BitVec.toInt_not, BitVec.toInt_eq_toNat_bmod]; simp only [Int.bmod]; split <;> split <;> omega
theorem bmod65 (a : Int) (h1 : -2 ^ 64 ≤ a) (h2 : a < 2 ^ 64) : a.bmod (2 ^ 65) = a := by
  simp only [Int.bmod]; split <;> omega
theorem sub_v (x y : BitVec 64) :
    (1#65 + (~~~BitVec.signExtend 65 y + BitVec.signExtend 65 x)).msb = decide (x.toInt - y.toInt < 0) := by
  have h1 := BitVec.toInt_lt (x := x); have h2 := BitVec.le_toInt (x := x)
  have h3 := BitVec.toInt_lt (x := y); have h4 := BitVec.le_toInt (x := y)
  rw [BitVec.msb_eq_toInt]
  congr 1
  rw [BitVec.toInt_add, BitVec.toInt_add, not65, BitVec.toInt_signExtend_of_le (show 64 ≤ 65 by omega),
    BitVec.toInt_signExtend_of_le (show 64 ≤ 65 by omega), show (1#65).toInt = 1 from by decide,
    bmod65 (-y.toInt - 1 + x.toInt) (by omega) (by omega), bmod65 _ (by omega) (by omega)]
  apply propext; constructor <;> intro h <;> omega
/-- overflow flag of `x - y` in both formulations -/
theorem sub_vflag (x y : BitVec 64) :
    ((1#65 + (~~~BitVec.signExtend 65 y + BitVec.signExtend 65 x)).msb != (x - y).msb) =
      !decide ((x.toInt - y.toInt).bmod 18446744073709551616 = x.toInt - y.toInt) := by
  have h1 := BitVec.toInt_lt (x := x); have h2 := BitVec.le_toInt (x := x)
  have h3 := BitVec.toInt_lt (x := y); have h4 := BitVec.le_toInt (x := y)
  rw [sub_v, BitVec.msb_eq_toInt, BitVec.toInt_sub]
  have e : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  rw [e]
  have ha1 : -18446744073709551616 < x.toInt - y.toInt := by omega
  have ha2 : x.toInt - y.toInt < 18446744073709551616 := by omega
  generalize x.toInt - y.toInt = a at *
  have hb : a.bmod 18446744073709551616 = a ∨ a.bmod 18446744073709551616 = a - 18446744073709551616 ∨
      a.bmod 18446744073709551616 = a + 18446744073709551616 := by simp only [Int.bmod]; split <;> omega
  have hr : -9223372036854775808 ≤ a.bmod 18446744073709551616 ∧ a.bmod 18446744073709551616 < 9223372036854775808 := by
    simp only [Int.bmod]; split <;> omega
  by_cases p : a < 0 <;> by_cases q : a.bmod 18446744073709551616 < 0 <;> by_cases r : a.bmod 18446744073709551616 = a <;>
    simp [p, q, r] <;> omega
/-! `cmp x, #0` (the only immediate compare we emit): the same sums with the constants folded -/
theorem imm0_res (x : BitVec 64) :
    BitVec.setWidth 64 (1#65 + (18446744073709551615#65 + BitVec.setWidth 65 x)) = x := by bv_omega
theorem imm0_c (x : BitVec 64) : (1#65 + (18446744073709551615#65 + BitVec.setWidth 65 x)).msb = true := by
  have hx := x.isLt
  simp only [BitVec.msb_eq_decide, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  simp; omega
theorem imm0_v (x : BitVec 64) : (1#65 + (36893488147419103231#65 + BitVec.signExtend 65 x)).msb = x.msb := by
  have h1 := BitVec.toInt_lt (x := x); have h2 := BitVec.le_toInt (x := x)
  rw [BitVec.msb_eq_toInt, BitVec.msb_eq_toInt]
  congr 1
  rw [BitVec.toInt_add, BitVec.toInt_add, BitVec.toInt_signExtend_of_le (show 64 ≤ 65 by omega),
    show (1#65).toInt = 1 from by decide, show (36893488147419103231#65).toInt = -1 from by decide,
    bmod65 (-1 + x.toInt) (by omega) (by omega), bmod65 _ (by omega) (by omega)]
  apply propext; constructor <;> intro h <;> omega
end Proven.Apc
