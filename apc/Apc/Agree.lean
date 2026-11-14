/- PROTOTYPE: the AlphaProof-Code semantics agrees with our small machine `armStep` on emitted words. -/
import Arm64
import Apc.Small
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

theorem vflag (x y : BitVec 64) : decide ((x.toInt - y.toInt).bmod 18446744073709551616 = x.toInt - y.toInt) =
    !BitVec.ssubOverflow x y := by
  have h1 := BitVec.toInt_lt (x := x); have h2 := BitVec.le_toInt (x := x)
  have h3 := BitVec.toInt_lt (x := y); have h4 := BitVec.le_toInt (x := y)
  have key : ((x.toInt - y.toInt).bmod 18446744073709551616 = x.toInt - y.toInt) ↔
      ¬ (x.toInt - y.toInt ≥ 2 ^ (64 - 1) ∨ x.toInt - y.toInt < -2 ^ (64 - 1)) := by
    simp only [Int.bmod]
    constructor <;> intro hh <;> (try split at hh) <;> (try split) <;> omega
  simp only [BitVec.ssubOverflow, key]
  simp
  by_cases a : x.toInt - y.toInt < 9223372036854775808 <;> by_cases b : -9223372036854775808 ≤ x.toInt - y.toInt <;>
    simp [a, b] <;> omega

macro "agree" : tactic => `(tactic| (
  refine ⟨_, rfl, fun s => ?_⟩
  simp +decide [Arm64.Program.evalInst, Arm64.execInstWithSvc, abs, armStep, AState.setX, AState.rd, AState.setSub, AState.cond,
    Arm64.RegWidth.ofBool, Arm64.Reg.fromZRBits, Arm64.Reg.fromSPBits, Arm64.AddSubOp.ofBits, Arm64.ShiftType.ofBits, Arm64.LogicalOp.ofBits,
    Arm64.CondSelectOp.ofBits, Arm64.CondCode.ofBits, Arm64.ConditionHolds,
    Arm64.State.readReg, Arm64.State.readReg64, Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.setPState,
    Arm64.State.advancePC, Arm64.RegFile.read, Arm64.RegFile.write, Arm64.evalAddSub, Arm64.evalLogical, Arm64.shiftVal, Arm64.shift64,
    Arm64.AddWithCarry64]
  all_goals try (refine ⟨?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩)
  all_goals try bv_omega
  all_goals try (simp only [BitVec.le_def.symm, decide_eq_true_eq]; bv_decide)
  all_goals try (rw [vflag]; bv_decide)
  all_goals try bv_decide
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
