/- PROTOTYPE: the AlphaProof-Code semantics agrees with our small machine `armStep` on emitted words. -/
import Arm64
import Apc.Small
import Apc.Flags
namespace Proven.Apc
open Proven.Arm

def Pg : Arm64.Program := Arm64.Program.ofSvc Arm64.noSyscalls
/-- their state seen as a small-machine state -/
def abs (s : Arm64.State) : AState where
  x := fun i => if i < 31 then s.regs.read (BitVec.ofNat 5 i) else 0
  n := s.pstate.n
  z := s.pstate.z
  c := s.pstate.c
  v := s.pstate.v

/-- word `w` decodes in their semantics, and executing it is `armStep w` on the abstraction, PC + 4,
memory / sp / status unchanged -/
def Agree (w : BitVec 32) : Prop :=
  ∃ i, Arm64.decode w = some i ∧ ∀ s : Arm64.State,
    abs (Pg.evalInst i s) = armStep w (abs s) ∧ (Pg.evalInst i s).pc = s.pc + 4 ∧
    (Pg.evalInst i s).mem = s.mem ∧ (Pg.evalInst i s).sp = s.sp ∧ (Pg.evalInst i s).status = s.status

theorem ofNat5 (i : Nat) (v : BitVec 5) (h : i < 31) : (BitVec.ofNat 5 i = v) = (i = v.toNat) := by
  apply propext; constructor
  · intro e; subst e; simp; omega
  · intro e; subst e; simp

macro "agree" : tactic => `(tactic| (
  refine ⟨_, rfl, fun s => ?_⟩
  simp +decide [Arm64.Program.evalInst, Arm64.execInstWithSvc, abs, armStep, AState.setX, AState.rd, AState.setSub, AState.cond,
    Arm64.RegWidth.ofBool, Arm64.Reg.fromZRBits, Arm64.Reg.fromSPBits, Arm64.AddSubOp.ofBits, Arm64.ShiftType.ofBits, Arm64.LogicalOp.ofBits,
    Arm64.CondSelectOp.ofBits, Arm64.CondCode.ofBits, Arm64.ConditionHolds,
    Arm64.State.readReg, Arm64.State.readReg64, Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.setPState,
    Arm64.State.advancePC, Arm64.RegFile.read, Arm64.RegFile.write, Arm64.evalAddSub, Arm64.evalLogical, Arm64.shiftVal, Arm64.shift64,
    Arm64.AddWithCarry64, sub_res, sub_c, imm0_res, imm0_c, imm0_v]
  all_goals try (refine ⟨?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩)
  all_goals try bv_omega
  all_goals try (rw [sub_vflag])
  all_goals try (exact beq_dec _ _)
  all_goals try (funext i; by_cases h : i < 31 <;> (try simp +decide [h, ofNat5 i _ h]) <;> (try split) <;> (try simp_all) <;> (try bv_omega))))

theorem agree_add : Agree 0x8B0A0129#32 := by agree   -- 21 emitted words of this class
theorem agree_sub : Agree 0xCB0A0129#32 := by agree   -- 10 emitted words of this class
theorem agree_subs : Agree 0xEB0A013F#32 := by agree   -- 10 emitted words of this class
theorem agree_and : Agree 0x8A0A0129#32 := by agree   -- 10 emitted words of this class
theorem agree_orr : Agree 0xAA0A0129#32 := by agree   -- 55 emitted words of this class
theorem agree_eor : Agree 0xCA0A0129#32 := by agree   -- 10 emitted words of this class
theorem agree_lslv : Agree 0x9ACA2129#32 := by agree   -- 10 emitted words of this class
theorem agree_lsrv : Agree 0x9ACA2529#32 := by agree   -- 10 emitted words of this class
theorem agree_asrv : Agree 0x9ACA2929#32 := by agree   -- 10 emitted words of this class
theorem agree_csel : Agree 0x9A8B1149#32 := by agree   -- 9 emitted words of this class
theorem agree_csinc : Agree 0x9A9F27E9#32 := by agree   -- 30 emitted words of this class
theorem agree_movz : Agree 0xD2800009#32 := by agree   -- 11 emitted words of this class
theorem agree_addimm : Agree 0x91000529#32 := by agree   -- 11 emitted words of this class
theorem agree_subsimm : Agree 0xF100013F#32 := by agree   -- 9 emitted words of this class
end Proven.Apc
