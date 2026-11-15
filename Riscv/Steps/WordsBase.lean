/- Simp normal forms for ALU results of the Sail model (were the header of the generated `Words.lean`, now
`Riscv/Legacy/Steps/Words.lean`); used by `sail_eval`-based proofs in `Branch.lean` and `Gen*.lean`. -/
import Spec.Code
import Riscv.Steps.Step
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven

@[simp] theorem log2_xlen_eq : Functions.log2_xlen = 6 := rfl
@[simp] theorem srl_eq {n m} (x : BitVec n) (y : BitVec m) : shift_bits_right x y = x >>> y.toNat := rfl
@[simp] theorem sra_eq {m} (x : BitVec 64) (y : BitVec m) : shift_bits_right_arith x y = x.sshiftRight y.toNat := by
  simp [shift_bits_right_arith]
@[simp] theorem bool_to_bit_ext (b : Bool) : zero_extend (m := 64) (bool_to_bit b) = if b then 1#64 else 0#64 := by
  cases b <;> rfl
@[simp] theorem ite_ult (a b : BitVec 64) :
    (if a.toNat < b.toNat then 1#64 else 0#64) = if a < b then 1#64 else 0#64 := by
  simp [BitVec.lt_def]
@[simp] theorem ite_slt (a b : BitVec 64) :
    (if a.toInt < b.toInt then 1#64 else 0#64) = if a.slt b then 1#64 else 0#64 := by
  simp [BitVec.slt_iff_toInt_lt]
@[simp] theorem ite_seqz (a : BitVec 64) :
    (if (a.toNat : Int) < 1 then 1#64 else 0#64) = if a = 0#64 then 1#64 else 0#64 := by
  have : (a.toNat : Int) < 1 ↔ a = 0#64 := by rw [← BitVec.toNat_inj]; simp; omega
  simp [this]
@[simp] theorem ite_snez (a : BitVec 64) :
    (if 0 < a.toNat then 1#64 else 0#64) = if a = 0#64 then 0#64 else 1#64 := by
  have : 0 < a.toNat ↔ ¬a = 0#64 := by rw [← BitVec.toNat_inj]; simp; omega
  by_cases ha : a = 0#64 <;> simp [ha, this]


end Proven
