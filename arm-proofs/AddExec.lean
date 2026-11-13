import Armv9.Instrs64
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem AddWithCarry_result {k_N : Nat} (x y : BitVec k_N) (c : BitVec 1) (h : 0 < k_N) : (AddWithCarry x y c).1 = x + y + c.zeroExtend k_N := by
  unfold AddWithCarry
  apply BitVec.eq_of_toNat_eq
  have h1 : (((x.toNat + y.toNat + c.toNat : Nat) : Int) % 2^(k_N+1)).toNat = (x.toNat+y.toNat+c.toNat) % 2^(k_N+1) := by norm_cast
  have e2 : k_N - 1 + 1 = k_N := by omega
  simp [integer_subrange, Sail.BitVec.length, get_slice_int]
  rw [e2]; push_cast at h1; rw [h1]
  simp [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_succ k_N))]
theorem add_x9_x10 (s : SequentialState RegisterType trivialChoiceSource) (a b : BitVec 64)
    (h9 : s.regs.get? Register.R9 = some a) (h10 : s.regs.get? Register.R10 = some b) :
    execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 9 64 10 9 false 0 .ShiftType_LSL false s
      = .ok () { s with regs := s.regs.insert Register.R9 (a + b) } := by
  simp [execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg, X_read, X_set, ShiftReg, get_R, set_R, read_gpr, write_gpr,
    PreSail.undefined_bitvector, PreSail.sail_assert, PreSail.choose, PreSail.readReg, PreSail.writeReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, h9, h10, AddWithCarry_result, Sail.BitVec.extractLsb, Sail.BitVec.zeroExtend]
  refine ⟨?_, rfl⟩
  have e : BitVec.extractLsb 63 0 a + BitVec.extractLsb 63 0 b <<< 0 = a + b := by
    simp [BitVec.extractLsb, BitVec.extractLsb']
  exact congrArg (fun v : BitVec 64 => s.regs.insert Register.R9 v) e
#print axioms add_x9_x10
