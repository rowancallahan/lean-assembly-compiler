/- Full-step machinery, part 2: address translation (MMU off at EL3) and the instruction fetch. -/
import Arm.Hooks
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.all false
set_option pp.deepTerms false
set_option pp.maxSteps 3000

namespace ArmProof

theorem aligned4 (va : BitVec 64) (h : va.toNat % 4 = 0) : IsAligned__1 va 4 = true := by
  have e : Align_int (BitVec.toNatInt va) 4 = (va.toNat : Int) := by
    simp only [Align_int, fdiv_int, BitVec.toNatInt]
    have h0 : ¬ ((va.toNat : Int) < 0) := by omega
    simp [h0, Int.tdiv_eq_ediv_of_nonneg (show (0:Int) ≤ va.toNat by omega)]
    omega
  simp only [IsAligned__1, Align_bits, Slice_int, e, get_slice_int, Sail.BitVec.length]
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_toNat_eq
  simp
  omega

/-- the word `w` sits little-endian at byte address `a` -/
def MemWord (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (w : BitVec 32) : Prop :=
  m.get? a = some (w.extractLsb' 0 8) ∧ m.get? (a+1) = some (w.extractLsb' 8 8) ∧
  m.get? (a+2) = some (w.extractLsb' 16 8) ∧ m.get? (a+3) = some (w.extractLsb' 24 8)
theorem w_split (w : BitVec 32) : (((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append (w.extractLsb' 0 8) = w := by
  ext i hi
  simp only [BitVec.append_eq, BitVec.getElem_append, BitVec.getElem_extractLsb']
  by_cases h1 : i < 8 <;> by_cases h2 : i < 16 <;> by_cases h3 : i < 24 <;> simp [h1, h2, h3]
  all_goals (repeat' split) <;> first | omega | (rw [BitVec.getLsbD_eq_getElem (by omega)] <;> (congr 1; omega))
theorem readBytes4 {s : St} {a : Nat} {w : BitVec 32} (h : MemWord s.mem a w) :
    (PreSail.readBytes 4 a : PreSailM RegisterType trivialChoiceSource exception _) s = .ok (w, none) s := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [PreSail.readBytes, PreSail.readByte, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, h0, h1, h2, h3, Nat.add_assoc]
  rw [w_split]

theorem dev_ne (va : BitVec 64) (h : va.toNat < 2 ^ 29) :
    BitVec.ofNat 40 (va.toNat >>> 16) ≠ ZeroExtend1 GIC_BASE ∧
    BitVec.ofNat 40 (va.toNat >>> 16) ≠ ZeroExtend1 UART_BASE := by
  have e1 : (ZeroExtend1 GIC_BASE : BitVec 40) = 0x2C00#40 := rfl
  have e2 : (ZeroExtend1 UART_BASE : BitVec 40) = 0x3C00#40 := rfl
  rw [e1, e2, Nat.shiftRight_eq_div_pow]
  constructor <;> intro hh <;> have := congrArg BitVec.toNat hh <;> simp at this <;> omega

theorem setw56 (va : BitVec 64) (h : va.toNat < 2 ^ 29) : (BitVec.setWidth 56 va).toNat = va.toNat := by
  simp; omega

theorem u_InstrEnc (s : St) : undefined___InstrEnc () s = .ok .__A64 s := rfl
theorem u_ExceptionRecord (s : St) : undefined_ExceptionRecord () s = .ok (uval (undefined_ExceptionRecord ())) s := rfl
theorem u_int (s : St) : (undefined_int () : SailM Int) s = .ok 0 s := rfl
theorem u_PhysMemRetStatus (s : St) : undefined_PhysMemRetStatus () s = .ok (uval (undefined_PhysMemRetStatus ())) s := rfl

section
variable {s : St} (hc : Pins s.regs)
include hc

theorem s1off_ok (va : BitVec 64) (fault : FaultRecord) (hfs : fault.statuscode = .Fault_None) (hva : va.toNat < 2 ^ 48) :
    ∃ r, AArch64_S1DisabledOutput fault .Regime_EL3 va accIF true s = .ok r { s with regs := s.regs.insert .InGuardedPage false } ∧
      r.1.statuscode = .Fault_None ∧ r.2.fault.statuscode = .Fault_None ∧ r.2.paddress.address = va.setWidth 56 := by
  have := walk_ok hc va; have := iz48 va hva; have hpm := @pamax_ok; pins
  simp only [AArch64_S1DisabledOutput, SetInGuardedPage, AArch64_S1ICacheEnabled, AArch64_AddrTop,
    AArch64_S1HasAlignmentFault, CreateAddressDescriptor, AArch64_S1DisabledOutputMECID, NoFault, accIF, wp3]
  gsimp

theorem s1en_ok (acc : AccessType) : AArch64_S1Enabled .Regime_EL3 acc s = .ok false s := by
  pins; simp only [AArch64_S1Enabled]; gsimp

theorem s1t_ok (va : BitVec 64) (fault : FaultRecord) (hfs : fault.statuscode = .Fault_None) (hva : va.toNat < 2 ^ 48) :
    ∃ r, AArch64_S1Translate fault .Regime_EL3 va true accIF s = .ok r { s with regs := s.regs.insert .InGuardedPage false } ∧
      r.1.statuscode = .Fault_None ∧ r.2.fault.statuscode = .Fault_None ∧ r.2.paddress.address = va.setWidth 56 := by
  obtain ⟨r, hr, h⟩ := s1off_ok hc va { fault with secondstage := false, s2fs1walk := false } hfs hva
  refine ⟨r, ?_, h⟩
  unfold AArch64_S1Translate
  rw [run_bind _ (uad_ok s), run_bind _ (ub_ok s), run_bind _ (ub_ok s), run_bind _ (u_TLBLine s)]
  dsimp only
  rw [run_bind _ (s1en_ok hc _)]
  simp only [Bool.not_false, if_true, run_lift]
  exact hr

theorem nofault_ok (acc : AccessDescriptor) : ∃ f, NoFault__1 acc s = .ok f s ∧ f.statuscode = .Fault_None := by
  pins; simp only [NoFault__1]; esimp

theorem fulltr_ok (va : BitVec 64) (hva : va.toNat < 2 ^ 48) :
    ∃ r, AArch64_FullTranslate va accIF true s = .ok r { s with regs := s.regs.insert .InGuardedPage false } ∧
      r.fault.statuscode = .Fault_None ∧ r.paddress.address = va.setWidth 56 := by
  obtain ⟨nf, hnf, hnfs⟩ := nofault_ok hc accIF
  obtain ⟨r, hr, h1, h2, h3⟩ := s1t_ok hc va nf hnfs hva
  refine ⟨r.2, ?_, h2, h3⟩
  unfold AArch64_FullTranslate
  have := regime_ok hc; have he := @el2en_ok
  have : accIF.el = 3#2 := rfl; have : accIF.ss = .SS_Secure := rfl; have : accIF.acctype = .AccessType_IFETCH := rfl
  esimp

theorem cdebug_ok (va : BitVec 64) (sz : Int) :
    ∃ f, AArch64_CheckDebug va accIF sz s = .ok f s ∧ f.statuscode = .Fault_None := by
  obtain ⟨nf, hnf, hnfs⟩ := nofault_ok hc accIF
  have := gde_ok hc; have := halted_ok hc; have := ss_el3 hc; have := el32_ok hc
  have : accIF.acctype = .AccessType_IFETCH := rfl; pins
  simp only [AArch64_CheckDebug, HaltOnBreakpointOrWatchpoint, HaltingAllowed, DoubleLockStatus, CurrentSecurityState,
    ExternalSecureInvasiveDebugEnabled, ExternalInvasiveDebugEnabled, IsDataAccess, EDSCR_read, edscrV]
  gsimp

theorem tr_ok (va : BitVec 64) (hva : va.toNat < 2 ^ 48) :
    ∃ r, AArch64_TranslateAddress va accIF true 4 s = .ok r { s with regs := s.regs.insert .InGuardedPage false } ∧
      r.fault.statuscode = .Fault_None ∧ r.paddress.address = va.setWidth 56 ∧ r.vaddress = va := by
  have hc' : Pins (s.regs.insert .InGuardedPage false) := (pins_insert _ rfl).2 hc
  obtain ⟨r, hr, h1, h2⟩ := fulltr_ok hc va hva
  obtain ⟨tsi, ht⟩ := tsi_ok hc va accIF 4
  obtain ⟨f, hf, hfs⟩ := cdebug_ok (s := { s with regs := s.regs.insert .InGuardedPage false }) hc' va 4
  have := regime_ok hc
  have : accIF.el = 3#2 := rfl; have : accIF.ss = .SS_Secure := rfl; have : accIF.acctype = .AccessType_IFETCH := rfl
  pins
  simp only [AArch64_TranslateAddress, IsFault, start_translation, end_translation,
    PreSail.sail_translation_start, PreSail.sail_translation_end]
  simp only [choice_unit] at hr hf
  esimp

theorem memread_ok (va : BitVec 64) (w : BitVec 32) (hva : va.toNat < 2 ^ 29) (hal : va.toNat % 4 = 0)
    (hw : MemWord s.mem va.toNat w) :
    AArch64_MemSingle_read va 4 accIF true s = .ok w { s with regs := s.regs.insert .InGuardedPage false } := by
  obtain ⟨r, hr, h1, h2, h3⟩ := tr_ok hc va (by omega)
  have := aligned4 va hal; have := dev_ne va hva; have := setw56 va hva; have := u_PhysMemRetStatus
  have := readBytes4 (s := { s with regs := s.regs.insert .InGuardedPage false }) hw
  have : accIF.tagchecked = false := rfl; have : accIF.exclusive = false := rfl
  pins
  simp only [AArch64_MemSingle_read, AArch64_MemSingle_read__1, IsFault, IsFault__2, PhysMemRead]
  simp only [choice_unit] at *
  esimp
  simp only [ConcurrencyInterfaceV1.sail_mem_read, PreSail.sail_mem_read, read_request, CreatePhysMemRetStatus] at *
  esimp

/-- **instruction fetch**: at `PC = pc` (4-aligned, below `2^29`) holding `w`, `__FetchInstr` returns `(A64, w)` and
writes only `BTypeCompatible := false`, `__InstructionStep := false`, `InGuardedPage := false` -/
theorem fetch_ok (pc : BitVec 64) (w : BitVec 32) (hpc : s.regs.get? ._PC = some pc) (hlt : pc.toNat < 2 ^ 29)
    (hal : pc.toNat % 4 = 0) (hw : MemWord s.mem pc.toNat w) (x : BitVec 64) :
    __FetchInstr x s = .ok (.__A64, w) { s with regs := ((s.regs.insert .BTypeCompatible false).insert .__InstructionStep false).insert .InGuardedPage false } := by
  have := ifetch_ok hc; have := u_InstrEnc; have := u_ExceptionRecord; have := u_int
  have : BitVec.setWidth 2 pc = 0#2 := by apply BitVec.eq_of_toNat_eq; simp; omega
  have hc1 : Pins (s.regs.insert .BTypeCompatible false) := (pins_insert _ rfl).2 hc
  have := sstep_ok (s := { s with regs := s.regs.insert .BTypeCompatible false }) hc1
  have hc2 : Pins ((s.regs.insert .BTypeCompatible false).insert .__InstructionStep false) := (pins_insert _ rfl).2 hc1
  have := memread_ok (s := { s with regs := (s.regs.insert .BTypeCompatible false).insert .__InstructionStep false }) hc2 pc w hlt hal hw
  pins
  simp only [__FetchInstr, SetBTypeCompatible, AArch64_CheckPCAlignment, ThisInstrAddr, PC_read, AArch64_CheckIllegalState, choice_unit] at *
  esimp

end
end ArmProof
