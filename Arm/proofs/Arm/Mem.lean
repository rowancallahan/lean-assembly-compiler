/- Data accesses (MMU off at EL3): `ldrb`/`strb`, aligned 64-bit `ldr`/`str`, `stur`, as full steps. -/
import Arm.BrFull
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.all false
set_option pp.deepTerms false
set_option pp.maxSteps 3000

namespace ArmProof

/-- the general-purpose load/store access descriptor at EL3 (`ld`: load, else store) -/
def accG (ld : Bool) : AccessDescriptor :=
  { acctype := AccessType.AccessType_GPR, el := 3#2, ss := SecurityState.SS_Secure, acqsc := false, acqpc := false,
    relsc := false, limitedordered := false, exclusive := false, atomicop := false, modop := accU.modop,
    nontemporal := false, read := ld, write := !ld, cacheop := accU.cacheop, opscope := accU.opscope,
    cachetype := accU.cachetype, pan := true, transactional := false, nonfault := false, firstfault := false,
    first := false, contiguous := false, streamingsve := false, ls64 := false, mops := false, rcw := false,
    rcws := false, toplevel := accU.toplevel, varange := accU.varange, a32lsmd := false, tagchecked := true,
    tagaccess := false, mpam := mpamV }

theorem readBytes1 {s : St} {a : Nat} {b : BitVec 8} (h : s.mem.get? a = some b) :
    (PreSail.readBytes 1 a : PreSailM RegisterType trivialChoiceSource exception _) s = .ok (b, none) s := by
  simp only [PreSail.readBytes, PreSail.readByte, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, h]

theorem u_Constraint (s : St) : undefined_Constraint () s = .ok (uval (undefined_Constraint ())) s := rfl

theorem alignedN (va : BitVec 64) (n : Nat) (hn : 0 < n) (h : va.toNat % n = 0) : IsAligned__1 va n = true := by
  have e : Align_int (BitVec.toNatInt va) n = (va.toNat : Int) := by
    simp only [Align_int, fdiv_int, BitVec.toNatInt]
    have h0 : ¬ ((va.toNat : Int) < 0) := by omega
    simp [h0, Int.tdiv_eq_ediv_of_nonneg (show (0:Int) ≤ va.toNat by omega)]
    have hd : (n : Int) ∣ (va.toNat : Int) := by exact_mod_cast Nat.dvd_of_mod_eq_zero h
    simp only [show ¬ ((n : Int) < 0) by omega, and_false, if_false]
    exact Int.ediv_mul_cancel hd
  simp only [IsAligned__1, Align_bits, Slice_int, e, get_slice_int, Sail.BitVec.length]
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_toNat_eq
  simp
  omega

theorem writeBytes1 (s : St) (a : Nat) (v : BitVec (8 * 1)) :
    (PreSail.writeBytes a v : PreSailM RegisterType trivialChoiceSource exception Bool) s =
      .ok true { s with mem := s.mem.insert a (v.extractLsb' 0 8) } := by
  simp [PreSail.writeBytes, PreSail.writeByte, List.ofFn, List.forM, bind, pure, EStateM.bind, EStateM.pure, modify,
    modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, Fin.foldr, Fin.foldr.loop]

theorem u_MemOp (s : St) : undefined_MemOp () s = .ok (uval (undefined_MemOp ())) s := rfl
theorem sz1 : ((((Int.shiftl 8 0).toNat : Int)).ediv 8).toNat = 1 := rfl
theorem sz8 : ((((Int.shiftl 8 3).toNat : Int)).ediv 8).toNat = 8 := rfl
theorem w8 : (Int.shiftl 8 0).toNat = 8 := rfl
theorem sz1' : (Int.ediv 8 8).toNat = 1 := rfl
theorem sz8' : (Int.ediv 64 8).toNat = 8 := rfl
theorem w64 : (Int.shiftl 8 3).toNat = 64 := rfl

section
variable {s : St} (hc : Pins s.regs)
include hc

theorem mpamG_ok : GenMPAMatEL .AccessType_GPR 3#2 s = .ok mpamV s := by
  have := ss_el3 hc; have := using32_ok hc; pins
  simp only [GenMPAMatEL, MPAMisEnabled, PARTIDspaceFromSS, DefaultMPAMinfo, MPAM3_EL3_read,
    undefined_MPAMinfo, undefined_PARTIDspaceType, mpamV]
  esimp

theorem gpr_ok (m : MemOp) (hm : m = .MemOp_LOAD ∨ m = .MemOp_STORE) :
    CreateAccDescGPR m false true true s = .ok (accG (m == .MemOp_LOAD)) s := by
  have := ss_el3 hc; have := mpamG_ok hc; have := uad_ok s; pins
  simp only [CreateAccDescGPR, NewAccDesc, GenMPAMcurEL, HaveTME]
  rcases hm with rfl | rfl <;> esimp <;> rfl


theorem s1offG_ok (ld : Bool) (va : BitVec 64) (fault : FaultRecord) (hfs : fault.statuscode = .Fault_None)
    (hva : va.toNat < 2 ^ 48) :
    ∃ r, AArch64_S1DisabledOutput fault .Regime_EL3 va (accG ld) true s = .ok r { s with regs := s.regs.insert .InGuardedPage false } ∧
      r.1.statuscode = .Fault_None ∧ r.2.fault.statuscode = .Fault_None ∧ r.2.paddress.address = va.setWidth 56 := by
  have := walk_ok hc va; have := iz48 va hva; have hpm := @pamax_ok; pins
  simp only [AArch64_S1DisabledOutput, SetInGuardedPage, AArch64_S1ICacheEnabled, AArch64_AddrTop,
    AArch64_S1HasAlignmentFault, CreateAddressDescriptor, AArch64_S1DisabledOutputMECID, NoFault, accG, wp3]
  gsimp


theorem s1tG_ok (ld : Bool) (va : BitVec 64) (fault : FaultRecord) (hfs : fault.statuscode = .Fault_None) (hva : va.toNat < 2 ^ 48) :
    ∃ r, AArch64_S1Translate fault .Regime_EL3 va true (accG ld) s = .ok r { s with regs := s.regs.insert .InGuardedPage false } ∧
      r.1.statuscode = .Fault_None ∧ r.2.fault.statuscode = .Fault_None ∧ r.2.paddress.address = va.setWidth 56 := by
  obtain ⟨r, hr, h⟩ := s1offG_ok hc ld va { fault with secondstage := false, s2fs1walk := false } hfs hva
  refine ⟨r, ?_, h⟩
  unfold AArch64_S1Translate
  rw [run_bind _ (uad_ok s), run_bind _ (ub_ok s), run_bind _ (ub_ok s), run_bind _ (u_TLBLine s)]
  dsimp only
  rw [run_bind _ (s1en_ok hc _)]
  simp only [Bool.not_false, if_true, run_lift]
  exact hr

theorem fulltrG_ok (ld : Bool) (va : BitVec 64) (hva : va.toNat < 2 ^ 48) :
    ∃ r, AArch64_FullTranslate va (accG ld) true s = .ok r { s with regs := s.regs.insert .InGuardedPage false } ∧
      r.fault.statuscode = .Fault_None ∧ r.paddress.address = va.setWidth 56 := by
  obtain ⟨nf, hnf, hnfs⟩ := nofault_ok hc (accG ld)
  obtain ⟨r, hr, h1, h2, h3⟩ := s1tG_ok hc ld va nf hnfs hva
  refine ⟨r.2, ?_, h2, h3⟩
  unfold AArch64_FullTranslate
  have := regime_ok hc; have he := @el2en_ok
  have : (accG ld).el = 3#2 := rfl; have : (accG ld).ss = .SS_Secure := rfl; have : (accG ld).acctype = .AccessType_GPR := rfl
  esimp

theorem cdebugG_ok (ld : Bool) (va : BitVec 64) (sz : Int) :
    ∃ f, AArch64_CheckDebug va (accG ld) sz s = .ok f s ∧ f.statuscode = .Fault_None := by
  obtain ⟨nf, hnf, hnfs⟩ := nofault_ok hc (accG ld)
  have := gde_ok hc; have := halted_ok hc; have := ss_el3 hc; have := el32_ok hc
  have : (accG ld).acctype = .AccessType_GPR := rfl; pins
  simp only [AArch64_CheckDebug, HaltOnBreakpointOrWatchpoint, HaltingAllowed, DoubleLockStatus, CurrentSecurityState,
    ExternalSecureInvasiveDebugEnabled, ExternalInvasiveDebugEnabled, IsDataAccess, EDSCR_read, edscrV]
  gsimp


theorem trG_ok (ld : Bool) (va : BitVec 64) (hva : va.toNat < 2 ^ 48) (sz : Int) :
    ∃ r, AArch64_TranslateAddress va (accG ld) true sz s = .ok r { s with regs := s.regs.insert .InGuardedPage false } ∧
      r.fault.statuscode = .Fault_None ∧ r.paddress.address = va.setWidth 56 ∧ r.vaddress = va := by
  have hc' : Pins (s.regs.insert .InGuardedPage false) := (pins_insert _ rfl).2 hc
  obtain ⟨r, hr, h1, h2⟩ := fulltrG_ok hc ld va hva
  obtain ⟨tsi, ht⟩ := tsi_ok hc va (accG ld) sz
  obtain ⟨f, hf, hfs⟩ := cdebugG_ok (s := { s with regs := s.regs.insert .InGuardedPage false }) hc' ld va sz
  have := regime_ok hc
  have : (accG ld).el = 3#2 := rfl; have : (accG ld).ss = .SS_Secure := rfl; have : (accG ld).acctype = .AccessType_GPR := rfl
  pins
  simp only [AArch64_TranslateAddress, IsFault, start_translation, end_translation,
    PreSail.sail_translation_start, PreSail.sail_translation_end]
  simp only [choice_unit] at hr hf
  esimp

theorem bigend_ok : BigEndian .AccessType_GPR s = .ok false s := by
  have := using32_ok hc; have := regime_ok hc; have := el32_ok hc; pins
  simp only [BigEndian, HaveNV2Ext, SCTLR_read__1, S1TranslationRegime__1, S1TranslationRegime, SCTLR_read, _get_SCTLRType_EE,
    _get_SCTLRType_E0E]
  gsimp

theorem memreadG1 (va : BitVec 64) (b : BitVec 8) (hva : va.toNat < 2 ^ 29) (hw : s.mem.get? va.toNat = some b) :
    Mem_read va 1 (accG true) s = .ok b { s with regs := s.regs.insert .InGuardedPage false } := by
  obtain ⟨r, hr, h1, h2, h3⟩ := trG_ok hc true va (by omega) 1
  have := dev_ne va hva; have := setw56 va hva; have := u_PhysMemRetStatus
  have := readBytes1 (s := { s with regs := s.regs.insert .InGuardedPage false }) hw
  have : (accG true).acctype = .AccessType_GPR := rfl; have : (accG true).tagchecked = true := rfl
  have : (accG true).exclusive = false := rfl; have : (accG true).atomicop = false := rfl; have : (accG true).acqsc = false := rfl
  have : (accG true).acqpc = false := rfl; have : (accG true).relsc = false := rfl; have : (accG true).transactional = false := rfl
  have := u_Constraint; have : IsAligned__1 va 1 = true := by simpa using alignedN va 1 (by decide) (by omega)
  pins
  simp only [Mem_read, Mem_read__2, AArch64_MemSingle_read__1, IsFault, IsFault__2, PhysMemRead]
  simp only [choice_unit] at *
  esimp
  have := bigend_ok (s := { s with regs := s.regs.insert .InGuardedPage false }) ((pins_insert _ rfl).2 hc)
  simp only [choice_unit] at this
  simp only [ConcurrencyInterfaceV1.sail_mem_read, PreSail.sail_mem_read, read_request, CreatePhysMemRetStatus] at *
  esimp


theorem memsetG1 (va : BitVec 64) (v : BitVec 8) (hva : va.toNat < 2 ^ 29) :
    Mem_set va 1 (accG false) v s = .ok () { s with regs := s.regs.insert .InGuardedPage false, mem := s.mem.insert va.toNat v } := by
  obtain ⟨r, hr, h1, h2, h3⟩ := trG_ok hc false va (by omega) 1
  have := dev_ne va hva; have := setw56 va hva; have := u_PhysMemRetStatus
  have : (accG false).acctype = .AccessType_GPR := rfl; have : (accG false).tagchecked = true := rfl
  have : (accG false).exclusive = false := rfl; have : (accG false).atomicop = false := rfl; have : (accG false).acqsc = false := rfl
  have : (accG false).acqpc = false := rfl; have : (accG false).relsc = false := rfl; have : (accG false).transactional = false := rfl
  have := u_Constraint; have : IsAligned__1 va 1 = true := by simpa using alignedN va 1 (by decide) (by omega)
  have := bigend_ok hc
  pins
  simp only [Mem_set, Mem_set__2, AArch64_MemSingle_set__1, IsFault, IsFault__2, PhysMemWrite]
  simp only [choice_unit] at *
  esimp
  have hwb := writeBytes1 { s with regs := s.regs.insert .InGuardedPage false } va.toNat v
  have e8 : BitVec.extractLsb' 0 8 v = v := by apply BitVec.eq_of_toNat_eq; simp
  rw [e8] at hwb; simp only [choice_unit] at hwb
  simp only [ConcurrencyInterfaceV1.sail_mem_write, PreSail.sail_mem_write, write_request, CreatePhysMemRetStatus] at *
  esimp


theorem spe_ld (s' : St) (h : s'.regs.get? .SPESampleInFlight = some false) : True := trivial

theorem ldrb_exec {t n : Nat} (ht : t < 31) (hn : n < 31) (imm : BitVec 12) {a : BitVec 64} (ha : xget s.regs n = some a)
    {b : BitVec 8} (hlt : (a + imm.setWidth 64).toNat < 2 ^ 29) (hb : s.mem.get? (a + imm.setWidth 64).toNat = some b) :
    decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned (BitVec.ofNat 5 t) (BitVec.ofNat 5 n) imm 1#2 0#2 s =
      .ok () { s with regs := xset (s.regs.insert .InGuardedPage false) t (b.setWidth 64) } := by
  idx t; idx n
  have hg := gpr_ok hc .MemOp_LOAD (.inl rfl)
  have hm := memreadG1 hc (a + imm.setWidth 64) b hlt hb
  simp only [decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned,
    execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx]
  have := u_MemOp; have := u_Constraint; have := read_gpr_ok ha
  have hn31 : (n == 31) = false := by simp; omega
  have hspe : (xset (s.regs.insert .InGuardedPage false) t (b.setWidth 64)).get? .SPESampleInFlight = some false := by
    rw [xset_get_ne _ _ _ _ (xreg_ne' (by decide))]; simp [Std.ExtDHashMap.get?_insert]; exact hc.spe
  pins
  exec_simp
  have hb31 : (n != 31) = true := by simp; omega
  simp only [choice_unit] at hm
  have hel0 : (3#2 != EL0) = true := by decide
  have hpf : (MemOp.MemOp_LOAD != MemOp.MemOp_PREFETCH) = true := by decide
  simp only [sz1, sz1', w8, hb31, hel0, hpf, Bool.and_true, BitVec.setWidth_eq]
  esimp
  simp only [sz1', hm, BitVec.setWidth_eq]
  esimp

end
end ArmProof
