/- The model's decode functions for the instructions the backend emits, run on symbolic register
numbers `d n m < 31`: each returns `ok` with the destination register (and, for `subs`, PSTATE.NZCV) updated. -/
import Arm.Base
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ArmProof

/-- facts about a register index `r < 31` in the forms the model's code tests them -/
macro "idx " r:ident : tactic => `(tactic| (
  have := Nat.mod_eq_of_lt (show $r < 32 by omega); have : $r ≠ 31 := (by omega)
  have : ($r : Int) ≤ 31 := (by omega); have : ($r : Int) ≠ 31 := (by omega)))

macro "exec_simp" : tactic => `(tactic| (simp (config := {decide := true}) [*, DecodeShift, X_read, X_set, ShiftReg, get_R, set_R,
  execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg, execute_aarch64_instrs_integer_logical_shiftedreg,
  execute_aarch64_instrs_integer_shift_variable, execute_aarch64_instrs_integer_conditional_select,
  execute_aarch64_instrs_integer_ins_ext_insert_movewide, execute_aarch64_instrs_integer_arithmetic_add_sub_immediate,
  PreSail.undefined_bitvector, PreSail.undefined_bool, undefined_LogicalOp, undefined_MoveWideOp, PreSail.internal_pick,
  PreSail.sail_assert, choose_ok, PreSail.readReg, PreSail.writeReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe,
  MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, Sail.BitVec.extractLsb,
  Sail.BitVec.zeroExtend, BitVec.extractLsb, BitVec.extractLsb', shl_int_zero, shl_int_mod, shr_int_mod, toNat_int_mod, shl_int_nat, shr_int_nat, nat_mod_eq, Zeros, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', AddWithCarry_64_0, AddWithCarry_64_sub, read_gpr_get, write_gpr_ok, insert_insert, setFlags, xset_get_ne, ConditionHolds, andM, Sail.BitVec.addInt]))

variable {s : St} {d n m : Nat} {a b : BitVec 64}

theorem add_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) :
    decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 0#6
      (BitVec.ofNat 5 m) 0#2 0#1 0#1 1#1 s = .ok () { s with regs := xset s.regs d (a + b) } := by
  idx d; idx n; idx m
  dsimp only [decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg]; dsimp
  exec_simp

theorem eor_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) :
    decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 0#6
      (BitVec.ofNat 5 m) 0#1 0#2 2#2 1#1 s = .ok () { s with regs := xset s.regs d (a ^^^ b) } := by
  idx d; idx n; idx m
  dsimp only [decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg]; dsimp
  exec_simp

theorem sub_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) :
    decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 0#6 (BitVec.ofNat 5 m) 0#2 0#1 1#1 1#1 s = .ok () { s with regs := xset s.regs d (a - b) } := by
  idx d; idx n; idx m
  dsimp only [decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg]; dsimp
  exec_simp

theorem and_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) :
    decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 0#6 (BitVec.ofNat 5 m) 0#1 0#2 0#2 1#1 s = .ok () { s with regs := xset s.regs d (a &&& b) } := by
  idx d; idx n; idx m
  dsimp only [decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg]; dsimp
  exec_simp

theorem orr_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) :
    decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 0#6 (BitVec.ofNat 5 m) 0#1 0#2 1#2 1#1 s = .ok () { s with regs := xset s.regs d (a ||| b) } := by
  idx d; idx n; idx m
  dsimp only [decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg]; dsimp
  exec_simp

theorem lslv_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) :
    decode_lslv_aarch64_instrs_integer_shift_variable (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 0#2 (BitVec.ofNat 5 m) 1#1 s = .ok () { s with regs := xset s.regs d (a <<< (b.toNat % 64)) } := by
  idx d; idx n; idx m
  dsimp only [decode_lslv_aarch64_instrs_integer_shift_variable]; dsimp
  exec_simp

theorem lsrv_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) :
    decode_lsrv_aarch64_instrs_integer_shift_variable (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 1#2 (BitVec.ofNat 5 m) 1#1 s = .ok () { s with regs := xset s.regs d (a >>> (b.toNat % 64)) } := by
  idx d; idx n; idx m
  dsimp only [decode_lsrv_aarch64_instrs_integer_shift_variable]; dsimp
  exec_simp

theorem asrv_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) :
    decode_asrv_aarch64_instrs_integer_shift_variable (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 2#2 (BitVec.ofNat 5 m) 1#1 s = .ok () { s with regs := xset s.regs d (a.sshiftRight (b.toNat % 64)) } := by
  idx d; idx n; idx m
  dsimp only [decode_asrv_aarch64_instrs_integer_shift_variable]; dsimp
  exec_simp

theorem mov_exec (hd : d < 31) (hm : m < 31) (hb : xget s.regs m = some b) :
    decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg (BitVec.ofNat 5 d) 31#5 0#6 (BitVec.ofNat 5 m) 0#1 0#2 1#2 1#1 s = .ok () { s with regs := xset s.regs d (b) } := by
  idx d; idx m
  dsimp only [decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg]; dsimp
  exec_simp

theorem movz_exec (hd : d < 31) :
    decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide (BitVec.ofNat 5 d) 0#16 0#2 2#2 1#1 s = .ok () { s with regs := xset s.regs d (0) } := by
  idx d
  dsimp only [decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide]; dsimp
  exec_simp

theorem inc_exec (hd : d < 31) (hn : n < 31) (ha : xget s.regs n = some a) :
    decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 1#12 0#1 0#1 0#1 1#1 s = .ok () { s with regs := xset s.regs d (a + 1) } := by
  idx d; idx n
  dsimp only [decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate]; dsimp
  exec_simp

theorem cmp_exec (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b)
    {p : ProcState} (hp : s.regs.get? .PSTATE = some p) :
    decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 (BitVec.ofNat 5 n) 0#6
      (BitVec.ofNat 5 m) 0#2 1#1 1#1 1#1 s = .ok () { s with regs := s.regs.insert .PSTATE (setFlags p (AddWithCarry a (~~~b) 1#1).2) } := by
  idx n; idx m
  dsimp only [decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg]; dsimp
  exec_simp

/-- `cmp xn, #i` (`subs xzr, xn, #i`); the immediate is kept symbolic (a literal `0#12` makes the kernel check blow up) -/
theorem cmp0_exec (i : BitVec 12) (hn : n < 31) (ha : xget s.regs n = some a) {p : ProcState} (hp : s.regs.get? .PSTATE = some p) :
    decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 (BitVec.ofNat 5 n) i 0#1 1#1 1#1 1#1 s
      = .ok () { s with regs := s.regs.insert .PSTATE (setFlags p (AddWithCarry a (~~~(i.zeroExtend 64)) 1#1).2) } := by
  idx n
  dsimp only [decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate]; dsimp
  exec_simp

variable {p : ProcState} (hp : s.regs.get? .PSTATE = some p) (hspe : s.regs.get? .SPESampleInFlight = some false)
include hp hspe

/-- `cset xd, lo` (`csinc xd, xzr, xzr, cs`) -/
theorem cset_lo_exec (hd : d < 31) :
    decode_csinc_aarch64_instrs_integer_conditional_select (BitVec.ofNat 5 d) 31#5 1#1 2#4 31#5 0#1 1#1 s
      = .ok () { s with regs := xset s.regs d (if p.C == 1#1 then 0 else 1) } := by
  idx d
  dsimp only [decode_csinc_aarch64_instrs_integer_conditional_select]; dsimp
  split <;> exec_simp

/-- `cset xd, lt` (`csinc xd, xzr, xzr, ge`) -/
theorem cset_lt_exec (hd : d < 31) :
    decode_csinc_aarch64_instrs_integer_conditional_select (BitVec.ofNat 5 d) 31#5 1#1 10#4 31#5 0#1 1#1 s
      = .ok () { s with regs := xset s.regs d (if p.N == p.V then 0 else 1) } := by
  idx d
  dsimp only [decode_csinc_aarch64_instrs_integer_conditional_select]; dsimp
  split <;> exec_simp

/-- `cset xd, eq` (`csinc xd, xzr, xzr, ne`) -/
theorem cset_eq_exec (hd : d < 31) :
    decode_csinc_aarch64_instrs_integer_conditional_select (BitVec.ofNat 5 d) 31#5 1#1 1#4 31#5 0#1 1#1 s
      = .ok () { s with regs := xset s.regs d (if p.Z == 1#1 then 1 else 0) } := by
  idx d
  dsimp only [decode_csinc_aarch64_instrs_integer_conditional_select]; dsimp
  split <;> exec_simp

/-- `csel xd, xn, xm, ne` -/
theorem csel_ne_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) :
    decode_csel_aarch64_instrs_integer_conditional_select (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 0#1 1#4 (BitVec.ofNat 5 m) 0#1 1#1 s
      = .ok () { s with regs := xset s.regs d (if p.Z == 1#1 then b else a) } := by
  idx d; idx n; idx m
  dsimp only [decode_csel_aarch64_instrs_integer_conditional_select]; dsimp
  split <;> exec_simp

end ArmProof
