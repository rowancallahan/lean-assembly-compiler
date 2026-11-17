/- Opt-in byte normal forms for S3 certificates (simp set `s3_bytes`, used by `s3_compileB`/`s3_compileF`), kept in
their own file so that adding one does not rebuild everything that imports `Compiler/S3/Cert.lean`. -/
import Compiler.S3.Cert

namespace Proven.S3

/-- a byte taken from a shifted word (`(x >>> k).toUInt8`, e.g. `le8`), in the form the program computes -/
@[s3_bytes] theorem u8_ofNat_shr (x : UInt64) (k : Nat) :
    BitVec.setWidth 64 (UInt8.ofNat (x.toNat >>> k)).toBitVec = x.toBitVec >>> k &&& 255#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, UInt8.toNat_toBitVec, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    UInt64.toNat_toBitVec]
  rw [show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have h : (UInt8.ofNat (x.toNat >>> k)).toNat = (x.toNat >>> k) % 256 := UInt8.toNat_ofNat
  rw [h]; omega

end Proven.S3
