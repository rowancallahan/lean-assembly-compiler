/- Sail ARMv9.4-A model (`Armv9`, Sail's Lean backend, Arm/model) as a Machine. Built by Arm/sail (not the root
project, which does not have the ARM model). -/
import Spec.Top
import Spec.Machines
import Armv9
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1

namespace Proven.Top

abbrev ArmSailState := SequentialState RegisterType trivialChoiceSource
abbrev ArmSailRegs := Std.ExtDHashMap Register RegisterType

/-- General register X0–X30 by number (31 = sp/xzr is not a data register here). -/
def armSailRegister (regs : ArmSailRegs) (number : Nat) : Option (BitVec 64) :=
  match number with
  | 0 => regs.get? .R0 | 1 => regs.get? .R1 | 2 => regs.get? .R2 | 3 => regs.get? .R3
  | 4 => regs.get? .R4 | 5 => regs.get? .R5 | 6 => regs.get? .R6 | 7 => regs.get? .R7
  | 8 => regs.get? .R8 | 9 => regs.get? .R9 | 10 => regs.get? .R10 | 11 => regs.get? .R11
  | 12 => regs.get? .R12 | 13 => regs.get? .R13 | 14 => regs.get? .R14 | 15 => regs.get? .R15
  | 16 => regs.get? .R16 | 17 => regs.get? .R17 | 18 => regs.get? .R18 | 19 => regs.get? .R19
  | 20 => regs.get? .R20 | 21 => regs.get? .R21 | 22 => regs.get? .R22 | 23 => regs.get? .R23
  | 24 => regs.get? .R24 | 25 => regs.get? .R25 | 26 => regs.get? .R26 | 27 => regs.get? .R27
  | 28 => regs.get? .R28 | 29 => regs.get? .R29 | 30 => regs.get? .R30
  | _ => none

/-- Missing values read as zero; register 31 (sp) reads as zero. -/
def armSailObserve (state : ArmSailState) : MachineState where
  programCounter := ((state.regs.get? ._PC).map UInt64.ofBitVec).getD 0
  register number := ((armSailRegister state.regs number).map UInt64.ofBitVec).getD 0
  memory address := (state.mem.get? address.toNat).map UInt8.ofBitVec

/-- One Sail `step_model` (elfmain.sail: `SEE = -1; __TopLevel(); __CycleEnd()`), else none. -/
noncomputable def armSailStep (state : ArmSailState) : Option ArmSailState :=
  match (do writeReg Register.SEE (-1 : Int); __TopLevel (); __CycleEnd () : SailM Unit) state with
  | .ok _ next => some next
  | .error _ _ => none

/-- Implemented features: only FEAT_AA64EL0 (index 4). -/
def armSailFeatures : Vector Bool 259 := Vector.ofFn (fun i => i.val == 4)

/-- Pinned system registers (from Arm/gen/pins.py): EL3, AArch64, MMU off, no pending interrupt, debug, PMU, SPE,
timers and BRBE off. -/
structure ArmSailPins (m : ArmSailRegs) : Prop where
  ps : ∃ p : ProcState, m.get? .PSTATE = some p ∧ p.EL = 3#2 ∧ p.nRW = 0#1 ∧ p.IL = 0#1
  feat : m.get? .FeatureImpl = some armSailFeatures
  scr : m.get? .SCR_EL3 = some 0
  edscr : m.get? ._EDSCR = some 0x02000002
  mdccsr : m.get? .MDCCSR_EL0 = some 0
  oslsr : m.get? .OSLSR_EL1 = some 0
  mdcr3 : m.get? .MDCR_EL3 = some 0
  gic : m.get? .__GIC_Pending = some none
  mpam3 : m.get? ._MPAM3_EL3 = some 0
  mpam2 : m.get? .MPAM2_EL2 = some 0
  pa : m.get? .__supported_pa_size = some 48
  tcr3 : m.get? .TCR_EL3 = some 0
  sctlr3 : m.get? .SCTLR_EL3 = some 0
  mair3 : m.get? .MAIR_EL3 = some 0
  mdscr : m.get? .MDSCR_EL1 = some 0
  spe : m.get? .SPESampleInFlight = some false
  dbgen : m.get? .DBGEN = some .Signal_Low
  spiden : m.get? .SPIDEN = some .Signal_Low
  edesr : m.get? .EDESR = some 0
  emu : m.get? .__emulator_termination_opcode = some none
  pmcr : m.get? .PMCR_EL0 = some 0
  mdcr2 : m.get? .MDCR_EL2 = some 0
  cntcr : m.get? .CNTCR = some 0
  cntp : m.get? .CNTP_CTL_EL0 = some 0
  cnthp : m.get? .CNTHP_CTL_EL2 = some 0
  cntps : m.get? .CNTPS_CTL_EL1 = some 0
  cntv : m.get? .CNTV_CTL_EL0 = some 0
  brbfcr : m.get? .BRBFCR_EL1 = some 0
  pcount : m.get? .PhysicalCount = some 0
  cnthpcv : m.get? .CNTHP_CVAL_EL2 = some 1


/-- Pinned registers, the branch bookkeeping a step reads, a cycle counter, X0–X30 and the pc present. -/
structure ArmSailConfigured (state : ArmSailState) : Prop where
  pins : ArmSailPins state.regs
  branchTaken : ∃ b, state.regs.get? .Branchtypetaken = some b ∧ (b == .BranchType_RESET) = false
  bTypeNext : ∃ n, state.regs.get? .BTypeNext = some n
  cycleCount : ∃ c, state.regs.get? .__cycle_count = some c
  registers : ∀ number < 31, (armSailRegister state.regs number).isSome
  pc : (state.regs.get? ._PC).isSome

noncomputable def armSail : Machine where
  State := ArmSailState
  step := armSailStep
  observe := armSailObserve
  configured := ArmSailConfigured
  mapping := armMapping
  ramStart := 0x80000000
  ramEnd := 0xC0000000

end Proven.Top
