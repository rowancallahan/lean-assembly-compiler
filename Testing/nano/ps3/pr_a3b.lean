import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
@[simp] theorem u64_toUInt8_bv (y : UInt64) : (y.toUInt8).toBitVec.setWidth 64 = y.toBitVec &&& 255 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  omega
@[simp] theorem u8_toUInt64_bv (a : UInt8) : a.toUInt64.toBitVec = a.toBitVec.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp
def a3 (bs : List UInt8) : List UInt8 := match bs with | a :: _ => Nano.mo 6 ((a.toUInt64 >>> 8).toUInt8) | [] => []
s3_compile Q := a3
end P
