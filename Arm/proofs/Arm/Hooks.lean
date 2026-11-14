/- Full-step machinery, part 1: the simp toolkit for the model's monad, the pinned feature set, and
lemmas for the configuration-reading helpers the fetch/execute loop calls. -/
import Arm.Base
import Armv9.Fetch
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.all false
set_option pp.deepTerms false
set_option pp.maxSteps 3000

namespace ArmProof

/-- The implemented-feature set `ArmFull` pins: only `FEAT_AA64EL0` (which makes `HaveAArch64` true).
Every other optional feature (MTE, SPE, PMU, RME, TME, BTI, PAuth, GCS, BRBE, VHE, SEL2, NMI, ...) is off. -/
def featOn : Feature → Bool
  | .FEAT_AA64EL0 => true
  | _ => false

/-- the `FeatureImpl` vector `ArmFull` pins -/
def featV : Vector Bool 259 := Vector.ofFn (fun i => i.val == 4)
theorem nf_lt (f : Feature) : (num_of_Feature f).toNat < 259 := by cases f <;> decide
theorem nf_on (f : Feature) : ((num_of_Feature f).toNat == 4) = featOn f := by cases f <;> rfl
theorem featV_get (f : Feature) : GetElem?.getElem! featV (num_of_Feature f) = featOn f := by
  show featV[(num_of_Feature f).toNat]! = featOn f
  rw [getElem!_pos featV _ (nf_lt f)]; simp [featV, nf_on]

theorem feat_ok {s : St} (h : s.regs.get? .FeatureImpl = some featV) (f : Feature) :
    IsFeatureImplemented f s = .ok (featOn f) s := by
  simp only [IsFeatureImplemented, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe,
    MonadStateOf.get, EStateM.get, h, featV_get]

/-- `EDSCR` value `ArmFull` pins: STATUS = 0b000010 (Non-debug state), PipeAdv (bit 25) = 1 -/
def edscrV : BitVec 32 := 0x02000002

theorem iz48 (va : BitVec 64) (h : va.toNat < 2 ^ 48) : is_zero_subrange va 63 48 = true := by
  have hm : (slice_mask (n := 64) 48 (63 - 48 + 1) : BitVec 64) = 0xFFFF000000000000#64 := by rfl
  simp only [is_zero_subrange, Sail.BitVec.length]
  rw [hm]
  have : va &&& 0xFFFF000000000000#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, BitVec.toNat_ofNat]
    by_cases hi : i < 48
    · have : (0xFFFF000000000000 % 2^64).testBit i = false := by
        rw [show (0xFFFF000000000000 % 2^64 : Nat) = 2^48 * 65535 from rfl, Nat.testBit_two_pow_mul]
        simp; omega
      simp [this]
    · have : va.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]
  rw [this]; decide

theorem z0 {w : Nat} (i : Nat) : (0#w)[i]! = false := by
  by_cases h : i < w
  · rw [getElem!_pos (0#w) i h]; simp
  · rw [getElem!_neg (0#w) i h]; rfl

theorem j1_zand {w : Nat} (y : BitVec w) (i : Nat) : BitVec.join1 [BitVec.access (0#w &&& y) i] = 0#1 := by
  rw [BitVec.zero_and]; simp [BitVec.join1, BitVec.access]; rw [z0]; rfl

open Lean Meta Simp in
/-- evaluate a closed `a == b` (enumerations with derived `BEq`, literals) by reduction -/
simproc beqClosed (BEq.beq _ _) := fun e => do
  if e.hasFVar || e.hasMVar then return .continue
  let r ← withTransparency .default <| whnf e
  if r.isConstOf ``true || r.isConstOf ``false then return .done { expr := r }
  return .continue

theorem pick_ok {α : Type} (a : α) (l : List α) (s : St) : (PreSail.internal_pick (a :: l) : SailM α) s = .ok a s := rfl

/-- stepping through a `SailME` block one lifted `SailM` action at a time (used with `rw`, so the untaken
branches of big definitions are never normalized) -/
theorem run_bind {β γ : Type} {m : SailM γ} (k : γ → SailME β β) {s s' : St} {a : γ} (h : m s = .ok a s') :
    SailME.run (liftM m >>= k) s = SailME.run (k a) s' := by
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, liftM, monadLift, MonadLift.monadLift, bind, ExceptT.bind,
    ExceptT.mk, ExceptT.lift, ExceptT.bindCont, EStateM.bind, EStateM.map, Functor.map, h]
theorem run_lift {β : Type} {m : SailM β} {s : St} : SailME.run (liftM m) s = m s := by
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, liftM, monadLift, MonadLift.monadLift, bind, ExceptT.lift,
    ExceptT.mk, EStateM.bind, EStateM.map, Functor.map, pure]
  cases m s <;> rfl
/-- the same for plain `SailM` blocks -/
theorem sm_bind {γ δ : Type} {m : SailM γ} (k : γ → SailM δ) {s s' : St} {a : γ} (h : m s = .ok a s') :
    (m >>= k) s = k a s' := by simp only [bind, EStateM.bind, h]
theorem ub_ok (s : St) : (undefined_bool () : SailM Bool) s = .ok false s := rfl

/-- the value `undefined_AccessDescriptor` returns (the trivial choice source picks the first constructor, `false`, `0`) -/
def accU : AccessDescriptor :=
  { acctype := .AccessType_IFETCH, el := 0, ss := .SS_NonSecure, acqsc := false, acqpc := false,
    relsc := false, limitedordered := false, exclusive := false, atomicop := false,
    modop := default, nontemporal := false, read := false, write := false,
    cacheop := default, opscope := default, cachetype := default, pan := false,
    transactional := false, nonfault := false, firstfault := false,
    first := false, contiguous := false, streamingsve := false, ls64 := false,
    mops := false, rcw := false, rcws := false, toplevel := false,
    varange := default, a32lsmd := false, tagchecked := false, tagaccess := false,
    mpam := { mpam_sp := .PIdSpace_Secure, partid := 0, pmg := 0 } }

/-- the value of a state-independent computation (the model's `undefined_*` generators), run on the default state -/
def uval {α : Type} [Inhabited α] (m : SailM α) : α :=
  match m (default : St) with
  | .ok a _ => a
  | .error _ _ => default

theorem u_TLBContext (s : St) : undefined_TLBContext () s = .ok (uval (undefined_TLBContext ())) s := rfl
theorem u_S1TTWParams (s : St) : undefined_S1TTWParams () s = .ok (uval (undefined_S1TTWParams ())) s := rfl
theorem u_AddressDescriptor (s : St) : undefined_AddressDescriptor () s = .ok (uval (undefined_AddressDescriptor ())) s := rfl
theorem u_FaultRecord (s : St) : undefined_FaultRecord () s = .ok (uval (undefined_FaultRecord ())) s := rfl
theorem u_MemoryAttributes (s : St) : undefined_MemoryAttributes () s = .ok (uval (undefined_MemoryAttributes ())) s := rfl
theorem u_FullAddress (s : St) : undefined_FullAddress () s = .ok (uval (undefined_FullAddress ())) s := rfl
theorem u_MemAttrHints (s : St) : undefined_MemAttrHints () s = .ok (uval (undefined_MemAttrHints ())) s := rfl
theorem u_GPCFRecord (s : St) : undefined_GPCFRecord () s = .ok (uval (undefined_GPCFRecord ())) s := rfl
theorem u_TLBLine (s : St) : undefined_TLBLine () s = .ok (uval (undefined_TLBLine ())) s := rfl
theorem u_SecurityState (s : St) : undefined_SecurityState () s = .ok .SS_NonSecure s := rfl
theorem u_TGx (s : St) : undefined_TGx () s = .ok (uval (undefined_TGx ())) s := rfl

theorem uad_ok (s : St) : undefined_AccessDescriptor () s = .ok accU s := rfl

-- BEGIN generated by gen/pins.py
/-- the pinned configuration registers (and the PSTATE fields) the full step relies on -/
structure Pins (m : Regs) : Prop where
  ps : ∃ p : ProcState, m.get? .PSTATE = some p ∧ p.EL = 3#2 ∧ p.nRW = 0#1 ∧ p.IL = 0#1
  feat : m.get? .FeatureImpl = some featV
  scr : m.get? .SCR_EL3 = some 0
  edscr : m.get? ._EDSCR = some edscrV
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

/-- `true` on registers outside `Pins` -/
def NotPinned (r : Register) : Bool := !(r == .PSTATE || r == .FeatureImpl || r == .SCR_EL3 || r == ._EDSCR || r == .MDCCSR_EL0 || r == .OSLSR_EL1 || r == .MDCR_EL3 || r == .__GIC_Pending || r == ._MPAM3_EL3 || r == .MPAM2_EL2 || r == .__supported_pa_size || r == .TCR_EL3 || r == .SCTLR_EL3 || r == .MAIR_EL3 || r == .MDSCR_EL1 || r == .SPESampleInFlight || r == .DBGEN || r == .SPIDEN || r == .EDESR || r == .__emulator_termination_opcode || r == .PMCR_EL0 || r == .MDCR_EL2 || r == .CNTCR || r == .CNTP_CTL_EL0 || r == .CNTHP_CTL_EL2 || r == .CNTPS_CTL_EL1 || r == .CNTV_CTL_EL0 || r == .BRBFCR_EL1 || r == .PhysicalCount || r == .CNTHP_CVAL_EL2)

theorem np_ne {r r' : Register} (h : NotPinned r = true) (h' : NotPinned r' = false) : ¬ (r == r') = true := by
  intro e; rw [beq_iff_eq] at e; subst e; rw [h] at h'; cases h'

theorem pins_insert {m : Regs} {r : Register} (v : RegisterType r) (h : NotPinned r = true) :
    Pins (m.insert r v) ↔ Pins m := by
  constructor <;> intro hc
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨p, hp, hpp⟩ := hc.ps; exact ⟨p, by simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .PSTATE) h rfl)] using hp, hpp⟩
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .FeatureImpl) h rfl)] using hc.feat
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .SCR_EL3) h rfl)] using hc.scr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := ._EDSCR) h rfl)] using hc.edscr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MDCCSR_EL0) h rfl)] using hc.mdccsr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .OSLSR_EL1) h rfl)] using hc.oslsr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MDCR_EL3) h rfl)] using hc.mdcr3
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .__GIC_Pending) h rfl)] using hc.gic
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := ._MPAM3_EL3) h rfl)] using hc.mpam3
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MPAM2_EL2) h rfl)] using hc.mpam2
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .__supported_pa_size) h rfl)] using hc.pa
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .TCR_EL3) h rfl)] using hc.tcr3
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .SCTLR_EL3) h rfl)] using hc.sctlr3
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MAIR_EL3) h rfl)] using hc.mair3
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MDSCR_EL1) h rfl)] using hc.mdscr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .SPESampleInFlight) h rfl)] using hc.spe
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .DBGEN) h rfl)] using hc.dbgen
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .SPIDEN) h rfl)] using hc.spiden
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .EDESR) h rfl)] using hc.edesr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .__emulator_termination_opcode) h rfl)] using hc.emu
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .PMCR_EL0) h rfl)] using hc.pmcr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MDCR_EL2) h rfl)] using hc.mdcr2
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTCR) h rfl)] using hc.cntcr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTP_CTL_EL0) h rfl)] using hc.cntp
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTHP_CTL_EL2) h rfl)] using hc.cnthp
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTPS_CTL_EL1) h rfl)] using hc.cntps
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTV_CTL_EL0) h rfl)] using hc.cntv
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .BRBFCR_EL1) h rfl)] using hc.brbfcr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .PhysicalCount) h rfl)] using hc.pcount
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTHP_CVAL_EL2) h rfl)] using hc.cnthpcv
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨p, hp, hpp⟩ := hc.ps; exact ⟨p, by simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .PSTATE) h rfl)] using hp, hpp⟩
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .FeatureImpl) h rfl)] using hc.feat
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .SCR_EL3) h rfl)] using hc.scr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := ._EDSCR) h rfl)] using hc.edscr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MDCCSR_EL0) h rfl)] using hc.mdccsr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .OSLSR_EL1) h rfl)] using hc.oslsr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MDCR_EL3) h rfl)] using hc.mdcr3
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .__GIC_Pending) h rfl)] using hc.gic
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := ._MPAM3_EL3) h rfl)] using hc.mpam3
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MPAM2_EL2) h rfl)] using hc.mpam2
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .__supported_pa_size) h rfl)] using hc.pa
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .TCR_EL3) h rfl)] using hc.tcr3
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .SCTLR_EL3) h rfl)] using hc.sctlr3
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MAIR_EL3) h rfl)] using hc.mair3
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MDSCR_EL1) h rfl)] using hc.mdscr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .SPESampleInFlight) h rfl)] using hc.spe
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .DBGEN) h rfl)] using hc.dbgen
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .SPIDEN) h rfl)] using hc.spiden
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .EDESR) h rfl)] using hc.edesr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .__emulator_termination_opcode) h rfl)] using hc.emu
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .PMCR_EL0) h rfl)] using hc.pmcr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .MDCR_EL2) h rfl)] using hc.mdcr2
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTCR) h rfl)] using hc.cntcr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTP_CTL_EL0) h rfl)] using hc.cntp
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTHP_CTL_EL2) h rfl)] using hc.cnthp
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTPS_CTL_EL1) h rfl)] using hc.cntps
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTV_CTL_EL0) h rfl)] using hc.cntv
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .BRBFCR_EL1) h rfl)] using hc.brbfcr
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .PhysicalCount) h rfl)] using hc.pcount
    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .CNTHP_CVAL_EL2) h rfl)] using hc.cnthpcv

theorem pins_pstate {m : Regs} (q : ProcState) (hq : q.EL = 3#2 ∧ q.nRW = 0#1 ∧ q.IL = 0#1) (hc : Pins m) :
    Pins (m.insert .PSTATE q) := by
  refine ⟨⟨q, by simp [Std.ExtDHashMap.get?_insert], hq⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.FeatureImpl) = true by decide)] using hc.feat
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.SCR_EL3) = true by decide)] using hc.scr
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register._EDSCR) = true by decide)] using hc.edscr
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.MDCCSR_EL0) = true by decide)] using hc.mdccsr
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.OSLSR_EL1) = true by decide)] using hc.oslsr
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.MDCR_EL3) = true by decide)] using hc.mdcr3
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.__GIC_Pending) = true by decide)] using hc.gic
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register._MPAM3_EL3) = true by decide)] using hc.mpam3
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.MPAM2_EL2) = true by decide)] using hc.mpam2
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.__supported_pa_size) = true by decide)] using hc.pa
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.TCR_EL3) = true by decide)] using hc.tcr3
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.SCTLR_EL3) = true by decide)] using hc.sctlr3
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.MAIR_EL3) = true by decide)] using hc.mair3
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.MDSCR_EL1) = true by decide)] using hc.mdscr
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.SPESampleInFlight) = true by decide)] using hc.spe
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.DBGEN) = true by decide)] using hc.dbgen
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.SPIDEN) = true by decide)] using hc.spiden
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.EDESR) = true by decide)] using hc.edesr
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.__emulator_termination_opcode) = true by decide)] using hc.emu
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.PMCR_EL0) = true by decide)] using hc.pmcr
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.MDCR_EL2) = true by decide)] using hc.mdcr2
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.CNTCR) = true by decide)] using hc.cntcr
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.CNTP_CTL_EL0) = true by decide)] using hc.cntp
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.CNTHP_CTL_EL2) = true by decide)] using hc.cnthp
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.CNTPS_CTL_EL1) = true by decide)] using hc.cntps
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.CNTV_CTL_EL0) = true by decide)] using hc.cntv
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.BRBFCR_EL1) = true by decide)] using hc.brbfcr
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.PhysicalCount) = true by decide)] using hc.pcount
  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.CNTHP_CVAL_EL2) = true by decide)] using hc.cnthpcv

set_option hygiene false in
/-- unpack `Pins s.regs` (named `hc`) into the atomic facts `esimp` rewrites with -/
macro "pins" : tactic => `(tactic| (obtain ⟨⟨p, hp, hel, hrw, hil⟩, h_feat, h_scr, h_edscr, h_mdccsr, h_oslsr, h_mdcr3, h_gic, h_mpam3, h_mpam2, h_pa, h_tcr3, h_sctlr3, h_mair3, h_mdscr, h_spe, h_dbgen, h_spiden, h_edesr, h_emu, h_pmcr, h_mdcr2, h_cntcr, h_cntp, h_cnthp, h_cntps, h_cntv, h_brbfcr, h_pcount, h_cnthpcv⟩ := id hc))
-- END generated

/-- re-inserting the value a register already holds changes nothing -/
theorem insert_self {m : Regs} {r : Register} {v : RegisterType r} (h : m.get? r = some v) : m.insert r v = m :=
  Std.ExtDHashMap.ext_get? fun k => by
    simp only [Std.ExtDHashMap.get?_insert]; split
    · rename_i e; have := eq_of_beq e; subst this; simp [h]
    · rfl

/-- the monad plumbing of the model (EStateM, the early-return `SailME` layer, try/catch) -/
macro "esimp" : tactic => `(tactic| (simp (config := {decide := true}) [*, featOn, feat_ok,
  PreSail.undefined_bitvector, PreSail.undefined_bool, PreSail.internal_pick,
  PreSail.sail_assert, choose_ok, PreSail.readReg, PreSail.writeReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe,
  MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, Sail.BitVec.extractLsb,
  Sail.BitVec.zeroExtend, BitVec.extractLsb, BitVec.extractLsb', andM, orM, ToBool.toBool, Std.ExtDHashMap.get?_insert,
  BitVec.zero_and, j1_zand, beqClosed, pick_ok, bne, pins_insert, NotPinned, u_TLBContext, u_S1TTWParams, u_AddressDescriptor,
  u_FaultRecord, u_MemoryAttributes, u_FullAddress, u_MemAttrHints, u_TGx, u_GPCFRecord, u_TLBLine, u_SecurityState, uad_ok,
  __UNKNOWN_AccessDescriptor, __UNKNOWN_AddressDescriptor, GPCNoFault, DEFAULT_MECID,
  SailME.run, SailME.throw, sailTryCatch, sailThrow, PreSail.sailTryCatch, PreSail.sailThrow, EStateM.tryCatch,
  EStateM.throw, Functor.map, EStateM.map, PreSail.PreSailME.run, PreSail.PreSailME.throw, ExceptT.run, ExceptT.bind,
  ExceptT.mk, ExceptT.lift, ExceptT.pure, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift, MonadExceptOf.throw,
  throwThe, ExceptT.instMonad,
  HaveEL, HaveAArch32, HaveAArch32EL, HighestEL, EL0, EL1, EL2, EL3, __IMPDEF_boolean, ImpDefBool, __IMPDEF_integer, ImpDefInt,
  HaveSecureEL2Ext, HaveVirtHostExt, HaveStatisticalProfilingv1p2, HaveFeatHPMN0, HavePMUv3ICNTR, HavePMUv3,
  HaveRME, HaveHPMDExt, HaveNoSecurePMUDisableOverride, HavePMUv3p5, HavePMUv3p7, HaveStatisticalProfilingv1p1,
  HaveStatisticalProfilingv1p4, HavePMUv3EDGE, HavePMUv3TH, HaveECVExt, HaveBRBEv1p1, HavePACExt, HaveTME,
  HaveBRBExt, HaveStatisticalProfiling, HaveSME, HaveGCS, HaveSVE, HaveBTIExt, HaveDITExt, HaveFeatNMI,
  HaveMTEExt, HavePANExt, HaveSSBSExt, HaveUAOExt, Havev8p9Debug, HaveDoubleLock, HavePMUv3p9, HavePFAR,
  HaveDoubleFaultExt, HaveIESB, HaveExtendedECDebugEvents, Havev8p8Debug, HaveNV2Ext, HaveNVExt, HaveFeatWFxT,
  HaveTWEDExt, HaveFeatHCX, HaveMTE4Ext, HaveMPAMv0p1Ext, HaveMPAMv1p1Ext, HaveCRCExt, HaveAESExt,
  HaveBit128PMULLExt, HaveSHA1Ext, HaveSHA256Ext, HaveSHA512Ext, HaveSHA3Ext, HaveSM3Ext, HaveSM4Ext,
  HaveRASExt, Have52BitIPAAndPASpaceExt, Have56BitPAExt, HaveMTE2Ext, HaveFeatLS64, HaveDoubleFault2Ext,
  HaveFeatSCTLR2, HaveAccessFlagUpdateExt, HaveAtomicExt, HaveDirtyBitModifierExt, HaveSMEFullA64, HaveAltFP,
  HaveFeatRPRES, HaveCNTSCExt, HaveMPAMExt, Have16bitVMID, AArch64_HaveHPDExt, HaveQRDMLAHExt,
  HaveCommonNotPrivateTransExt, HaveExtendedExecuteNeverExt, AArch32_HaveHPDExt, Have52BitVAExt, Have52BitPAExt,
  HaveV82Debug, HaveTrapLoadStoreMultipleDeviceExt, HaveFJCVTZSExt, HaveFCADDExt, HaveDOTPExt,
  HaveSmallTranslationTableExt, HaveLSE2Ext, HaveFP16MulNoRoundingToFP32Ext, HaveFlagManipulateExt,
  HaveFlagFormatExt, HaveSelfHostedTrace, HaveBlockBBM, Havev8p4Debug, HaveStage2MemAttrControl, HaveIDSExt,
  HaveFrintExt, HaveE0PDExt, HaveGTGExt, HaveSBExt, HaveMTEAsyncExt, HaveMTEPermExt, HaveDGHExt, HaveBF16Ext,
  HaveEBF16, HaveAArch32BF16Ext, HaveFGTExt, HaveInt8MatMulExt, HaveAArch32Int8MatMulExt, HavePMUv3p4, HaveDoPD,
  Have56BitVAExt, Have128BitDescriptorExt, HaveAIEExt, HaveFeatTCR2, HavePAN3Ext, HaveMTEAsymFaultExt,
  HaveFeatLS64_V, HaveFeatLS64_ACCDATA, HaveFeatXS, HaveFeatEBEP, HaveStatisticalProfilingFDS, HaveFeatHBC,
  HaveFeatMOPS, HaveFeatTIDCP1, HaveFeatCMOW, HaveMTECanonicalTagCheckingExt, HaveLRCPC3Ext,
  HaveMTEStoreOnlyExt, HaveCSSC, HaveS1PIExt, HaveS1POExt, HaveS2PIExt, HaveS2POExt, HaveFeatCLRBHB, HaveTHExt,
  HaveLSE128, HaveSysReg128, HaveSysInstr128, HaveRASv2Ext, HaveFeatMEC, HaveAccessFlagUpdateForTableExt,
  HaveFeatABLE, HaveEnhancedPAC, HaveEnhancedPAC2, HaveFPAC, HaveFPACCombined, ConstPACField,
  HavePACQARMA3Generic, HavePACQARMA3Auth, HavePACQARMA5Generic, HavePACQARMA5Auth, HavePACIMPGeneric,
  HavePACIMPAuth, HaveSVEFP32MatMulExt, HaveSVEFP64MatMulExt, HaveSVE2, HaveSVE2AES, HaveSVE2PMULL128,
  HaveSVE2SHA3, HaveSVE2SM4, HaveSVE2BitPerm, HaveSVE2p1, HaveSVEB16B16, HaveSMEF64F64, HaveSMEI16I64, HaveSME2,
  HaveSME2p1, HaveSMEB16B16, HaveSMEF16F16]))

/-- `esimp` plus the field getters of the pinned system registers -/
macro "gsimp" : tactic => `(tactic| ((try simp only [
  _get_BRBFCR_EL1_Type_bits, _get_CNTCR_Type_bits, _get_CNTHP_CTL_EL2_Type_bits, _get_CNTPS_CTL_EL1_Type_bits,
  _get_CNTP_CTL_EL0_Type_bits, _get_CNTV_CTL_EL0_Type_bits, _get_EDESR_Type_bits, _get_EDSCR_Type_bits,
  _get_HCR_EL2_Type_bits, _get_MAIRType_bits, _get_MDCR_EL2_Type_bits, _get_MDCR_EL3_Type_bits,
  _get_MDSCR_EL1_Type_bits, _get_MPAM3_EL3_Type_bits, _get_OSLSR_EL1_Type_bits, _get_PMBSR_EL1_Type_bits,
  _get_PMCR_EL0_Type_bits, _get_SCRType_bits, _get_SCR_EL3_Type_bits, _get_SCTLRType_bits,
  _get_SCTLR_EL3_Type_bits, _get_TCR_EL3_Type_bits, _get_TTBR0_EL3_Type_bits, _get_EDSCR_Type_RW,
  _get_HCR_EL2_Type_RW, _get_SCRType_RW, _get_SCR_EL3_Type_RW, _get_SCRType_AW, _get_SCRType_EA,
  _get_PMBSR_EL1_Type_EA, _get_SCR_EL3_Type_EA, _get_SCRType_FIQ, _get_SCR_EL3_Type_FIQ, _get_SCRType_FW,
  _get_SCRType_HCE, _get_SCR_EL3_Type_HCE, _get_SCRType_IRQ, _get_SCR_EL3_Type_IRQ, _get_SCRType_NS,
  _get_EDSCR_Type_NS, _get_SCR_EL3_Type_NS, _get_SCRType_SCD, _get_SCRType_SIF, _get_SCR_EL3_Type_SIF,
  _get_SCRType_SMD, _get_SCR_EL3_Type_SMD, _get_SCRType_ST, _get_SCR_EL3_Type_ST, _get_SCRType_TWE,
  _get_HCR_EL2_Type_TWE, _get_SCR_EL3_Type_TWE, _get_SCRType_TWI, _get_HCR_EL2_Type_TWI, _get_SCR_EL3_Type_TWI,
  _get_SCRType_nET, _get_SCTLRType_A, _get_EDSCR_Type_A, _get_SCTLR_EL3_Type_A, _get_SCTLRType_C,
  _get_PMCR_EL0_Type_C, _get_SCTLR_EL3_Type_C, _get_SCTLRType_CP15BEN, _get_SCTLRType_DSSBS,
  _get_SCTLR_EL3_Type_DSSBS, _get_SCTLRType_DZE, _get_SCTLRType_E0E, _get_SCTLRType_EE, _get_SCTLR_EL3_Type_EE,
  _get_SCTLRType_EPAN, _get_SCTLRType_I, _get_SCTLR_EL3_Type_I, _get_SCTLRType_IESB, _get_SCTLR_EL3_Type_IESB,
  _get_SCTLRType_ITD, _get_SCTLRType_M, _get_SCTLR_EL3_Type_M, _get_SCTLRType_NMI, _get_SCTLR_EL3_Type_NMI,
  _get_SCTLRType_SA, _get_SCTLR_EL3_Type_SA, _get_SCTLRType_SA0, _get_SCTLRType_SED, _get_SCTLRType_SPAN,
  _get_SCTLRType_SPINTMASK, _get_SCTLR_EL3_Type_SPINTMASK, _get_SCTLRType_TIDCP, _get_HCR_EL2_Type_TIDCP,
  _get_SCTLRType_TME, _get_HCR_EL2_Type_TME, _get_SCR_EL3_Type_TME, _get_SCTLR_EL3_Type_TME,
  _get_SCTLRType_TME0, _get_SCTLRType_TMT, _get_SCTLR_EL3_Type_TMT, _get_SCTLRType_TMT0, _get_SCTLRType_TSCXT,
  _get_SCTLRType_UCI, _get_SCTLRType_UCT, _get_SCTLRType_UMA, _get_SCTLRType_WXN, _get_SCTLR_EL3_Type_WXN,
  _get_SCTLRType_nAA, _get_SCTLR_EL3_Type_nAA, _get_SCTLRType_nTWE, _get_SCTLRType_nTWI, _get_MAIRType_Attr0,
  _get_MAIRType_Attr1, _get_MAIRType_Attr2, _get_MAIRType_Attr3, _get_MAIRType_Attr4, _get_MAIRType_Attr5,
  _get_MAIRType_Attr6, _get_MAIRType_Attr7, _get_EDESR_Type_EC, _get_PMBSR_EL1_Type_EC, _get_EDSCR_Type_EL,
  _get_BRBFCR_EL1_Type_LASTFAILED, _get_PMCR_EL0_Type_N, _get_HCR_EL2_Type_AMO, _get_HCR_EL2_Type_AMVOFFEN,
  _get_SCR_EL3_Type_AMVOFFEN, _get_HCR_EL2_Type_API, _get_SCR_EL3_Type_API, _get_HCR_EL2_Type_APK,
  _get_SCR_EL3_Type_APK, _get_HCR_EL2_Type_AT, _get_HCR_EL2_Type_ATA, _get_SCR_EL3_Type_ATA,
  _get_SCTLR_EL3_Type_ATA, _get_HCR_EL2_Type_BSU, _get_HCR_EL2_Type_CD, _get_HCR_EL2_Type_DC,
  _get_HCR_EL2_Type_DCT, _get_HCR_EL2_Type_E2H, _get_HCR_EL2_Type_EnSCXT, _get_SCR_EL3_Type_EnSCXT,
  _get_HCR_EL2_Type_FB, _get_HCR_EL2_Type_FIEN, _get_SCR_EL3_Type_FIEN, _get_HCR_EL2_Type_FMO,
  _get_HCR_EL2_Type_FWB, _get_HCR_EL2_Type_GPF, _get_SCR_EL3_Type_GPF, _get_HCR_EL2_Type_HCD,
  _get_HCR_EL2_Type_ID, _get_HCR_EL2_Type_IMO, _get_HCR_EL2_Type_MIOCNCE, _get_HCR_EL2_Type_NV,
  _get_HCR_EL2_Type_NV1, _get_HCR_EL2_Type_NV2, _get_HCR_EL2_Type_PTW, _get_HCR_EL2_Type_SWIO,
  _get_HCR_EL2_Type_TACR, _get_HCR_EL2_Type_TDZ, _get_HCR_EL2_Type_TEA, _get_HCR_EL2_Type_TERR,
  _get_SCR_EL3_Type_TERR, _get_HCR_EL2_Type_TGE, _get_HCR_EL2_Type_TICAB, _get_HCR_EL2_Type_TID0,
  _get_HCR_EL2_Type_TID1, _get_HCR_EL2_Type_TID2, _get_HCR_EL2_Type_TID3, _get_HCR_EL2_Type_TID4,
  _get_HCR_EL2_Type_TID5, _get_HCR_EL2_Type_TLOR, _get_SCR_EL3_Type_TLOR, _get_HCR_EL2_Type_TOCU,
  _get_HCR_EL2_Type_TPC, _get_HCR_EL2_Type_TPCP, _get_HCR_EL2_Type_TPU, _get_HCR_EL2_Type_TRVM,
  _get_HCR_EL2_Type_TSC, _get_HCR_EL2_Type_TSW, _get_HCR_EL2_Type_TTLB, _get_HCR_EL2_Type_TTLBIS,
  _get_HCR_EL2_Type_TTLBOS, _get_HCR_EL2_Type_TVM, _get_HCR_EL2_Type_TWEDEL, _get_SCR_EL3_Type_TWEDEL,
  _get_HCR_EL2_Type_TWEDEn, _get_SCR_EL3_Type_TWEDEn, _get_HCR_EL2_Type_VF, _get_HCR_EL2_Type_VI,
  _get_HCR_EL2_Type_VM, _get_HCR_EL2_Type_VSE, _get_SCR_EL3_Type_ADEn, _get_SCR_EL3_Type_AIEn,
  _get_SCR_EL3_Type_D128En, _get_SCR_EL3_Type_EASE, _get_SCR_EL3_Type_ECVEn, _get_SCR_EL3_Type_EEL2,
  _get_SCR_EL3_Type_EnAS0, _get_SCR_EL3_Type_EnIDCP128, _get_SCR_EL3_Type_EnTP2, _get_SCR_EL3_Type_FGTEn,
  _get_SCR_EL3_Type_FGTEn2, _get_SCR_EL3_Type_GCSEn, _get_SCR_EL3_Type_HXEn, _get_SCR_EL3_Type_MECEn,
  _get_SCR_EL3_Type_NMEA, _get_SCR_EL3_Type_NSE, _get_EDSCR_Type_NSE, _get_SCR_EL3_Type_PFAREn,
  _get_SCR_EL3_Type_PIEn, _get_SCR_EL3_Type_RCWMASKEn, _get_SCR_EL3_Type_SCTLR2En, _get_SCR_EL3_Type_TCR2En,
  _get_SCR_EL3_Type_TMEA, _get_SCR_EL3_Type_TRNDR, _get_SCR_EL3_Type_TWERR, _get_MDCR_EL2_Type_HCCD,
  _get_MDCR_EL2_Type_HLP, _get_MDCR_EL2_Type_HPMD, _get_MDCR_EL2_Type_HPME, _get_MDCR_EL2_Type_HPMFZO,
  _get_MDCR_EL2_Type_HPMN, _get_MDCR_EL2_Type_MTPME, _get_MDCR_EL3_Type_MTPME, _get_EDSCR_Type_TDA,
  _get_MDCR_EL2_Type_TDA, _get_MDCR_EL3_Type_TDA, _get_MDSCR_EL1_Type_TDA, _get_MDCR_EL2_Type_TDCC,
  _get_MDCR_EL3_Type_TDCC, _get_MDSCR_EL1_Type_TDCC, _get_MDCR_EL2_Type_TDE, _get_MDCR_EL2_Type_TDOSA,
  _get_MDCR_EL3_Type_TDOSA, _get_MDCR_EL2_Type_TDRA, _get_MDCR_EL2_Type_TPM, _get_MDCR_EL3_Type_TPM,
  _get_MDCR_EL2_Type_TPMCR, _get_MDCR_EL2_Type_TTRF, _get_MDCR_EL3_Type_TTRF, _get_MDCR_EL2_Type_E2PB,
  _get_MDCR_EL2_Type_EBWE, _get_MDCR_EL3_Type_EBWE, _get_MDCR_EL2_Type_EnSPM, _get_MDSCR_EL1_Type_EnSPM,
  _get_MDCR_EL2_Type_HPMFZS, _get_MDCR_EL2_Type_PMEE, _get_MDCR_EL3_Type_PMEE, _get_MDCR_EL2_Type_PMSSE,
  _get_MDCR_EL3_Type_PMSSE, _get_MDCR_EL2_Type_TPMS, _get_EDSCR_Type_ERR, _get_MDSCR_EL1_Type_ERR,
  _get_EDSCR_Type_HDE, _get_MDSCR_EL1_Type_HDE, _get_EDSCR_Type_INTdis, _get_MDSCR_EL1_Type_INTdis,
  _get_EDSCR_Type_ITE, _get_EDSCR_Type_ITO, _get_EDSCR_Type_MA, _get_EDSCR_Type_PipeAdv, _get_EDSCR_Type_RXO,
  _get_MDSCR_EL1_Type_RXO, _get_EDSCR_Type_RXfull, _get_MDSCR_EL1_Type_RXfull, _get_EDSCR_Type_SC2,
  _get_MDSCR_EL1_Type_SC2, _get_EDSCR_Type_SDD, _get_MDCR_EL3_Type_SDD, _get_EDSCR_Type_STATUS,
  _get_EDSCR_Type_TFO, _get_MDSCR_EL1_Type_TFO, _get_EDSCR_Type_TXU, _get_MDSCR_EL1_Type_TXU,
  _get_EDSCR_Type_TXfull, _get_MDSCR_EL1_Type_TXfull, _get_PMCR_EL0_Type_D, _get_PMCR_EL0_Type_DP,
  _get_PMCR_EL0_Type_E, _get_PMCR_EL0_Type_FZO, _get_PMCR_EL0_Type_FZS, _get_PMCR_EL0_Type_IDCODE,
  _get_PMCR_EL0_Type_IMP, _get_PMCR_EL0_Type_LC, _get_PMCR_EL0_Type_LP, _get_PMCR_EL0_Type_P,
  _get_PMCR_EL0_Type_X, _get_MDCR_EL3_Type_E3BREC, _get_MDCR_EL3_Type_E3BREW, _get_MDCR_EL3_Type_EDAD,
  _get_MDCR_EL3_Type_EDADE, _get_MDCR_EL3_Type_EPMAD, _get_MDCR_EL3_Type_EPMADE, _get_MDCR_EL3_Type_EPMSSAD,
  _get_MDCR_EL3_Type_EnPM2, _get_MDCR_EL3_Type_EnPMS3, _get_MDCR_EL3_Type_EnPMSN, _get_MDCR_EL3_Type_EnPMSS,
  _get_MDCR_EL3_Type_MCCD, _get_MDCR_EL3_Type_MPMX, _get_MDCR_EL3_Type_NSPB, _get_MDCR_EL3_Type_NSPBE,
  _get_MDCR_EL3_Type_RLTE, _get_MDCR_EL3_Type_SBRBE, _get_MDCR_EL3_Type_SCCD, _get_MDCR_EL3_Type_SPD32,
  _get_MDCR_EL3_Type_SPME, _get_MDCR_EL3_Type_STE, _get_BRBFCR_EL1_Type_BANK, _get_BRBFCR_EL1_Type_CONDDIR,
  _get_BRBFCR_EL1_Type_DIRCALL, _get_BRBFCR_EL1_Type_DIRECT, _get_BRBFCR_EL1_Type_EnI,
  _get_BRBFCR_EL1_Type_INDCALL, _get_BRBFCR_EL1_Type_INDIRECT, _get_BRBFCR_EL1_Type_PAUSED,
  _get_BRBFCR_EL1_Type_RTN, _get_EDESR_Type_SS, _get_MDSCR_EL1_Type_SS, _get_TCR_EL3_Type_DS,
  _get_TCR_EL3_Type_HA, _get_TCR_EL3_Type_HD, _get_TCR_EL3_Type_IRGN0, _get_TCR_EL3_Type_ORGN0,
  _get_TCR_EL3_Type_SH0, _get_TCR_EL3_Type_T0SZ, _get_TCR_EL3_Type_TG0, _get_TCR_EL3_Type_HPD,
  _get_TCR_EL3_Type_HWU59, _get_TCR_EL3_Type_HWU60, _get_TCR_EL3_Type_HWU61, _get_TCR_EL3_Type_HWU62,
  _get_TCR_EL3_Type_MTX, _get_TCR_EL3_Type_PS, _get_TCR_EL3_Type_TBI, _get_TCR_EL3_Type_TBID,
  _get_TCR_EL3_Type_TCMA, _get_TCR_EL3_Type_AIE, _get_TCR_EL3_Type_D128, _get_TCR_EL3_Type_DisCH0,
  _get_TCR_EL3_Type_HAFT, _get_TCR_EL3_Type_PIE, _get_TCR_EL3_Type_POE, _get_TCR_EL3_Type_PTTWI,
  _get_TCR_EL3_Type_PnCH, _get_PMBSR_EL1_Type_AssuredOnly, _get_PMBSR_EL1_Type_COLL, _get_PMBSR_EL1_Type_DL,
  _get_PMBSR_EL1_Type_DirtyBit, _get_PMBSR_EL1_Type_MSS, _get_PMBSR_EL1_Type_Overlay, _get_PMBSR_EL1_Type_S,
  _get_MDSCR_EL1_Type_EHBWE, _get_MDSCR_EL1_Type_EMBWE, _get_MDSCR_EL1_Type_KDE, _get_MDSCR_EL1_Type_MDE,
  _get_OSLSR_EL1_Type_OSLK, _get_OSLSR_EL1_Type_OSLM, _get_OSLSR_EL1_Type_nTT, _get_SCTLR_EL3_Type_BT,
  _get_SCTLR_EL3_Type_EIS, _get_SCTLR_EL3_Type_EOS, _get_SCTLR_EL3_Type_EnDA, _get_SCTLR_EL3_Type_EnDB,
  _get_SCTLR_EL3_Type_EnIA, _get_SCTLR_EL3_Type_EnIB, _get_SCTLR_EL3_Type_ITFSB, _get_SCTLR_EL3_Type_TCF,
  _get_SCTLR_EL3_Type_TCSO, _get_EDESR_Type_OSUC, _get_EDESR_Type_RC, _get_MPAM3_EL3_Type_ALTSP_HFC,
  _get_MPAM3_EL3_Type_MPAMEN, _get_MPAM3_EL3_Type_PARTID_D, _get_MPAM3_EL3_Type_PARTID_I,
  _get_MPAM3_EL3_Type_PMG_D, _get_MPAM3_EL3_Type_PMG_I, _get_MPAM3_EL3_Type_ALTSP_EL3,
  _get_MPAM3_EL3_Type_ALTSP_HEN, _get_MPAM3_EL3_Type_FORCE_NS, _get_MPAM3_EL3_Type_RT_ALTSP_NS,
  _get_MPAM3_EL3_Type_SDEFLT, _get_MPAM3_EL3_Type_TRAPLOWER, _get_TTBR0_EL3_Type_CnP, _get_TTBR0_EL3_Type_SKL,
  _get_CNTCR_Type_EN, _get_CNTHP_CTL_EL2_Type_ENABLE, _get_CNTPS_CTL_EL1_Type_ENABLE,
  _get_CNTP_CTL_EL0_Type_ENABLE, _get_CNTV_CTL_EL0_Type_ENABLE, _get_CNTHP_CTL_EL2_Type_IMASK,
  _get_CNTPS_CTL_EL1_Type_IMASK, _get_CNTP_CTL_EL0_Type_IMASK, _get_CNTV_CTL_EL0_Type_IMASK,
  _get_CNTHP_CTL_EL2_Type_ISTATUS, _get_CNTPS_CTL_EL1_Type_ISTATUS, _get_CNTP_CTL_EL0_Type_ISTATUS,
  _get_CNTV_CTL_EL0_Type_ISTATUS, _get_CNTCR_Type_FCREQ, _get_CNTCR_Type_HDBG, _get_CNTCR_Type_SCEN] at *); esimp))


section
variable {s : St} (hc : Pins s.regs)
include hc

theorem aa64_ok : HaveAArch64 () s = .ok true s := by pins; simp only [HaveAArch64]; esimp
theorem ss_el3 : SecurityStateAtEL 3#2 s = .ok .SS_Secure s := by pins; simp only [SecurityStateAtEL]; esimp
theorem using32_ok : UsingAArch32 () s = .ok false s := by pins; simp only [UsingAArch32, HaveAArch64]; esimp
theorem el2en_ok : EL2Enabled () s = .ok false s := by
  pins; simp only [EL2Enabled, SCR_GEN_read, IsSecureEL2Enabled, Mk_SCRType, _get_SCRType_NS, HaveAArch64]; esimp
theorem secbelow_ok : IsSecureBelowEL3 () s = .ok true s := by
  pins; simp only [IsSecureBelowEL3, SCR_GEN_read, Mk_SCRType, _get_SCRType_NS, HaveAArch64]; esimp
theorem el32_ok (el : BitVec 2) (h : el ≠ 0#2) : ELUsingAArch32 el s = .ok false s := by
  have := secbelow_ok hc; pins
  simp only [ELUsingAArch32, ELStateUsingAArch32, ELStateUsingAArch32K]; esimp
theorem halted_ok : Halted () s = .ok false s := by
  pins; simp only [Halted, EDSCR_read, _get_EDSCR_Type_STATUS, edscrV]; esimp
theorem gde_ok : AArch64_GenerateDebugExceptions () s = .ok false s := by
  have := ss_el3 hc; have := halted_ok hc; have := el32_ok hc; pins
  simp only [AArch64_GenerateDebugExceptions, AArch64_GenerateDebugExceptionsFrom, CurrentSecurityState,
    DoubleLockStatus, IsSecureEL2Enabled, _get_OSLSR_EL1_Type_OSLK]; esimp
theorem dtarget_ok : DebugTarget () s = .ok 1#2 s := by
  have := ss_el3 hc; have := el32_ok hc; pins
  simp only [DebugTarget, DebugTargetFrom, CurrentSecurityState, HaveAArch64]; esimp
theorem sstep_ok : CheckSoftwareStep () s = .ok () { s with regs := s.regs.insert .__InstructionStep false } := by
  have := gde_ok hc; have := dtarget_ok hc; have := el32_ok hc; pins
  simp only [CheckSoftwareStep]; esimp
theorem take_ok (req : InterruptReq) : TakePendingInterrupts req s = .ok false s := by
  have := using32_ok hc; pins
  simp only [TakePendingInterrupts, AArch64_PendingUnmaskedVirtualInterrupts, AArch64_PendingUnmaskedPhysicalInterrupts,
    IRQPending, FIQPending, IsPhysicalSErrorPending, __GIC_InterruptPending, EL2Enabled,
    SCR_GEN_read, IsSecureEL2Enabled, Mk_SCRType, _get_SCRType_NS, HaveAArch64]
  esimp

/-- the MPAM info of every access at EL3 -/
def mpamV : MPAMinfo := { mpam_sp := .PIdSpace_Secure, partid := DefaultPARTID, pmg := DefaultPMG }

theorem mpam_ok : GenMPAMatEL .AccessType_IFETCH 3#2 s = .ok mpamV s := by
  have := ss_el3 hc; have := using32_ok hc; pins
  simp only [GenMPAMatEL, MPAMisEnabled, PARTIDspaceFromSS, DefaultMPAMinfo, MPAM3_EL3_read,
    undefined_MPAMinfo, undefined_PARTIDspaceType, mpamV]
  esimp

/-- the instruction-fetch access descriptor at EL3 -/
def accIF : AccessDescriptor := { accU with acctype := .AccessType_IFETCH, el := 3#2, ss := .SS_Secure, mpam := mpamV }

theorem ifetch_ok : CreateAccDescIFetch () s = .ok accIF s := by
  have := ss_el3 hc; have := mpam_ok hc; have := uad_ok s; pins
  simp only [CreateAccDescIFetch, NewAccDesc, GenMPAMcurEL]
  esimp; rfl

theorem pamax_ok : AArch64_PAMax () s = .ok 48 s := by
  pins; simp only [AArch64_PAMax]; esimp

theorem regime_ok : TranslationRegime 3#2 s = .ok .Regime_EL3 s := by
  have := el32_ok hc; pins; simp only [TranslationRegime]; esimp

theorem tsi_ok (va : BitVec 64) (acc : AccessDescriptor) (sz : Int) :
    ∃ v, AArch64_GetTranslationStartInfo .Regime_EL3 .SS_Secure acc va sz s = .ok v s := by
  pins
  simp only [AArch64_GetTranslationStartInfo, AArch64_GetS1TLBContext, AArch64_TLBContextEL3]
  esimp

def uS1 : S1TTWParams := uval (undefined_S1TTWParams ())
/-- the stage-1 walk parameters at EL3 with `TCR_EL3 = SCTLR_EL3 = MAIR_EL3 = 0` -/
def wp3 : S1TTWParams := { uS1 with ha := 0, hd := 0, tbi := 0, tbid := 0, d128 := 0, aie := 0, ds := 0, ps := 0, txsz := 0, pnch := 0, disch := 0, haft := 0, mtx := 0, skl := 0, pie := 0, emec := 0, tgx := .TGx_4KB, irgn := 0, orgn := 0, sh := 0, hpd := 0, ee := 0, wxn := 0, sif := 0, mair := 0 }

theorem walk_ok (va : BitVec 64) : AArch64_GetS1TTWParams .Regime_EL3 .SS_Secure va s = .ok wp3 s := by
  pins
  simp only [AArch64_GetS1TTWParams, AArch64_S1TTWParamsEL3, AArch64_S1DecodeTG0, AArch64_HaveS1TG, Mk_MAIRType]
  gsimp; rfl

end
end ArmProof
