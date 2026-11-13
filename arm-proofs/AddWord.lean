import Armv9.DecodeEnd
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
theorem AddWithCarry_result {k_N : Nat} (x y : BitVec k_N) (c : BitVec 1) (h : 0 < k_N) : (AddWithCarry x y c).1 = x + y + c.zeroExtend k_N := by
  unfold AddWithCarry
  apply BitVec.eq_of_toNat_eq
  have h1 : (((x.toNat + y.toNat + c.toNat : Nat) : Int) % 2^(k_N+1)).toNat = (x.toNat+y.toNat+c.toNat) % 2^(k_N+1) := by norm_cast
  have e2 : k_N - 1 + 1 = k_N := by omega
  simp [integer_subrange, Sail.BitVec.length, get_slice_int]
  rw [e2]; push_cast at h1; rw [h1]
  simp [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_succ k_N))]
theorem shl_int_zero {w : Nat} (b : BitVec w) : b <<< (0 : Int) = b := by
  show BitVec.shiftLeft b 0 = b
  simp [BitVec.shiftLeft]
theorem add_word (s : SequentialState RegisterType trivialChoiceSource) (pc : Int) (see : Int) (hs : see < 1)
    (h : s.regs.get? Register.SEE = some see) (a b : BitVec 64)
    (h9 : s.regs.get? Register.R9 = some a) (h10 : s.regs.get? Register.R10 = some b) :
    ∃ s', __DecodeA64_DataProcReg pc 0x8b0a0129#32 s = .ok () s' ∧ s'.regs = (s.regs.insert Register.SEE (14 : Int)).insert Register.R9 (a + b) ∧ s'.mem = s.mem := by
  have h14 : see < 14 := by omega
  simp (config := {decide := true}) [__DecodeA64_DataProcReg, decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg, DecodeShift, andM, ToBool.toBool, BitVec.slice,
    execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg, X_read, X_set, ShiftReg, get_R, set_R, read_gpr, write_gpr,
    PreSail.undefined_bitvector, PreSail.sail_assert, PreSail.choose, PreSail.readReg, PreSail.writeReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, h, hs, h14, h9, h10, AddWithCarry_result, Sail.BitVec.extractLsb, Sail.BitVec.zeroExtend, BitVec.extractLsb, BitVec.extractLsb', Std.ExtDHashMap.get?_insert]
  exact congrArg (fun v : BitVec 64 => (s.regs.insert Register.SEE (14 : Int)).insert Register.R9 v) (by change a + (b <<< (0:Int)) = a + b; rw [shl_int_zero])
#print axioms add_word
