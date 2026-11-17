import Riscv.Frontx.S3IO
theorem u8_mk_sw (x : BitVec 64) : (⟨x.setWidth 8⟩ : UInt8) = UInt8.ofNat x.toNat := by
  apply UInt8.toNat_inj.mp; simp; omega
theorem u64_toUInt8_ofNat (y : UInt64) : y.toUInt8 = UInt8.ofNat y.toNat := rfl
example (h : UInt8) : (⟨BitVec.setWidth 8 (BitVec.setWidth 64 h.toBitVec >>> 8)⟩ : UInt8) = (h.toUInt64 >>> 8).toUInt8 := by
  simp [u8_mk_sw, u64_toUInt8_ofNat]
