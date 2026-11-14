/- The result formats of compiled pipes are the spec encodings of `Proven/Encode.lean`:
a byte result is `enc b` (by `rfl`), a word result (`leBytes w 8`) is `enc w`. -/
import Spec.Encode
import Compiler.Front.Pipe

namespace Proven

theorem leByte (w : BitVec 64) (j : Nat) :
    (⟨(w >>> (8 * j)).setWidth 8⟩ : UInt8) = UInt8.ofNat (w.toNat / 256 ^ j % 256) := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', Nat.mod_mod_of_dvd _ (by decide)]
  show ((w >>> (8 * j)).setWidth 8).toNat = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- the word-fold output format is the spec encoding of a 64-bit word -/
theorem leBytes_eq_enc (w : BitVec 64) : leBytes w 8 = enc w := by
  show _ = leN 8 w.toNat
  simp only [leBytes, List.range, List.range.loop, List.map, leN, leByte]
  simp [Nat.div_div_eq_div_mul]

theorem byte_eq_enc (b : UInt8) : [b] = enc b := rfl

end Proven
