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

theorem fin64 (i : Nat) (h : i < 64) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega

/-- the doubleword `v` sits little-endian at byte address `a` -/
def MemD (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) : Prop :=
  ∀ i < 8, m.get? (a + i) = some (v.extractLsb' (8 * i) 8)

theorem d_split (v : BitVec 64) : (((((((v.extractLsb' 56 8).append (v.extractLsb' 48 8)).append (v.extractLsb' 40 8)).append
    (v.extractLsb' 32 8)).append (v.extractLsb' 24 8)).append (v.extractLsb' 16 8)).append (v.extractLsb' 8 8)).append
    (v.extractLsb' 0 8) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.append_eq, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have : i < 64 := hi
  rcases fin64 i this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp

theorem readBytes8 {s : St} {a : Nat} {v : BitVec 64} (h : MemD s.mem a v) :
    (PreSail.readBytes 8 a : PreSailM RegisterType trivialChoiceSource exception _) s = .ok (v, none) s := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  have h4 := h 4 (by omega); have h5 := h 5 (by omega); have h6 := h 6 (by omega); have h7 := h 7 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [PreSail.readBytes, PreSail.readByte, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, h0, h1, h2, h3, h4, h5, h6, h7, Nat.add_assoc]
  rw [d_split]

/-- the memory after writing the doubleword `v` little-endian at `a` -/
def wrD (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) : Std.ExtHashMap Nat (BitVec 8) :=
  (List.range 8).foldl (fun m i => m.insert (a + i) (v.extractLsb' (8 * i) 8)) m

theorem writeBytes8 (s : St) (a : Nat) (v : BitVec (8 * 8)) :
    (PreSail.writeBytes a v : PreSailM RegisterType trivialChoiceSource exception Bool) s =
      .ok true { s with mem := wrD s.mem a v } := by
  simp [PreSail.writeBytes, PreSail.writeByte, List.ofFn, List.forM, bind, pure, EStateM.bind, EStateM.pure, modify,
    modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, Fin.foldr, Fin.foldr.loop, wrD, List.range, List.range.loop]

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

theorem memreadG1 (va : BitVec 64) (b : BitVec 8) (hva : VaOK va.toNat) (hw : s.mem.get? va.toNat = some b) :
    Mem_read va 1 (accG true) s = .ok b { s with regs := s.regs.insert .InGuardedPage false } := by
  obtain ⟨r, hr, h1, h2, h3⟩ := trG_ok hc true va hva.1 1
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


theorem memsetG1 (va : BitVec 64) (v : BitVec 8) (hva : VaOK va.toNat) :
    Mem_set va 1 (accG false) v s = .ok () { s with regs := s.regs.insert .InGuardedPage false, mem := s.mem.insert va.toNat v } := by
  obtain ⟨r, hr, h1, h2, h3⟩ := trG_ok hc false va hva.1 1
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


theorem ldrb_exec {t n : Nat} (ht : t < 31) (hn : n < 31) (imm : BitVec 12) {a : BitVec 64} (ha : xget s.regs n = some a)
    {b : BitVec 8} (hlt : VaOK (a + imm.setWidth 64).toNat) (hb : s.mem.get? (a + imm.setWidth 64).toNat = some b) :
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


theorem strb_exec {t n : Nat} (ht : t < 31) (hn : n < 31) (imm : BitVec 12) {a v : BitVec 64} (ha : xget s.regs n = some a)
    (hv : xget s.regs t = some v) (hlt : VaOK (a + imm.setWidth 64).toNat) :
    decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned (BitVec.ofNat 5 t) (BitVec.ofNat 5 n) imm 0#2 0#2 s =
      .ok () { s with regs := s.regs.insert .InGuardedPage false, mem := s.mem.insert (a + imm.setWidth 64).toNat (v.setWidth 8) } := by
  idx t; idx n
  have hg := gpr_ok hc .MemOp_STORE (.inr rfl)
  have hm := memsetG1 hc (a + imm.setWidth 64) (v.setWidth 8) hlt
  have := u_MemOp; have := u_Constraint; have := read_gpr_ok ha; have := read_gpr_ok hv
  have hn31 : (n == 31) = false := by simp; omega
  have hspe : (s.regs.insert .InGuardedPage false).get? .SPESampleInFlight = some false := by
    simp [Std.ExtDHashMap.get?_insert]; exact hc.spe
  simp only [decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned,
    execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx]
  pins
  exec_simp
  have hb31 : (n != 31) = true := by simp; omega
  simp only [choice_unit] at hm
  have hel0 : (3#2 != EL0) = true := by decide
  have hpf : (MemOp.MemOp_STORE != MemOp.MemOp_PREFETCH) = true := by decide
  simp only [sz1, sz1', w8, hb31, hel0, hpf, Bool.and_true, BitVec.setWidth_eq]
  esimp
  simp only [sz1', hm, BitVec.setWidth_eq]
  esimp


theorem memreadG8 (va : BitVec 64) (v : BitVec 64) (hva : VaOK va.toNat) (hal : va.toNat % 8 = 0)
    (hw : MemD s.mem va.toNat v) :
    Mem_read va 8 (accG true) s = .ok v { s with regs := s.regs.insert .InGuardedPage false } := by
  obtain ⟨r, hr, h1, h2, h3⟩ := trG_ok hc true va hva.1 8
  have := dev_ne va hva; have := setw56 va hva; have := u_PhysMemRetStatus
  have := readBytes8 (s := { s with regs := s.regs.insert .InGuardedPage false }) hw
  have : (accG true).acctype = .AccessType_GPR := rfl; have : (accG true).tagchecked = true := rfl
  have : (accG true).exclusive = false := rfl; have : (accG true).atomicop = false := rfl; have : (accG true).acqsc = false := rfl
  have : (accG true).acqpc = false := rfl; have : (accG true).relsc = false := rfl; have : (accG true).transactional = false := rfl
  have := u_Constraint; have : IsAligned__1 va 8 = true := by simpa using alignedN va 8 (by decide) hal
  pins
  simp only [Mem_read, Mem_read__2, AArch64_MemSingle_read__1, IsFault, IsFault__2, PhysMemRead]
  simp only [choice_unit] at *
  esimp
  have := bigend_ok (s := { s with regs := s.regs.insert .InGuardedPage false }) ((pins_insert _ rfl).2 hc)
  simp only [choice_unit] at this
  simp only [ConcurrencyInterfaceV1.sail_mem_read, PreSail.sail_mem_read, read_request, CreatePhysMemRetStatus] at *
  esimp

theorem memsetG8 (va : BitVec 64) (v : BitVec 64) (hva : VaOK va.toNat) (hal : va.toNat % 8 = 0) :
    Mem_set va 8 (accG false) v s = .ok () { s with regs := s.regs.insert .InGuardedPage false, mem := wrD s.mem va.toNat v } := by
  obtain ⟨r, hr, h1, h2, h3⟩ := trG_ok hc false va hva.1 8
  have := dev_ne va hva; have := setw56 va hva; have := u_PhysMemRetStatus
  have : (accG false).acctype = .AccessType_GPR := rfl; have : (accG false).tagchecked = true := rfl
  have : (accG false).exclusive = false := rfl; have : (accG false).atomicop = false := rfl; have : (accG false).acqsc = false := rfl
  have : (accG false).acqpc = false := rfl; have : (accG false).relsc = false := rfl; have : (accG false).transactional = false := rfl
  have := u_Constraint; have : IsAligned__1 va 8 = true := by simpa using alignedN va 8 (by decide) hal
  have := bigend_ok hc
  pins
  simp only [Mem_set, Mem_set__2, AArch64_MemSingle_set__1, IsFault, IsFault__2, PhysMemWrite]
  simp only [choice_unit] at *
  esimp
  have hwb := writeBytes8 { s with regs := s.regs.insert .InGuardedPage false } va.toNat v
  simp only [choice_unit] at hwb
  simp only [ConcurrencyInterfaceV1.sail_mem_write, PreSail.sail_mem_write, write_request, CreatePhysMemRetStatus] at *
  esimp


theorem ldr_exec {t n : Nat} (ht : t < 31) (hn : n < 31) (imm : BitVec 12) {a : BitVec 64} (ha : xget s.regs n = some a)
    {v : BitVec 64} (hlt : VaOK (a + imm.setWidth 64 <<< 3).toNat) (hal : (a + imm.setWidth 64 <<< 3).toNat % 8 = 0)
    (hv : MemD s.mem (a + imm.setWidth 64 <<< 3).toNat v) :
    decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned (BitVec.ofNat 5 t) (BitVec.ofNat 5 n) imm 1#2 3#2 s =
      .ok () { s with regs := xset (s.regs.insert .InGuardedPage false) t v } := by
  idx t; idx n
  have hg := gpr_ok hc .MemOp_LOAD (.inl rfl)
  have hm := memreadG8 hc (a + imm.setWidth 64 <<< 3) v hlt hal hv
  have := u_MemOp; have := u_Constraint; have := read_gpr_ok ha
  have hn31 : (n == 31) = false := by simp; omega
  have hspe : (xset (s.regs.insert .InGuardedPage false) t v).get? .SPESampleInFlight = some false := by
    rw [xset_get_ne _ _ _ _ (xreg_ne' (by decide))]; simp [Std.ExtDHashMap.get?_insert]; exact hc.spe
  simp only [decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned,
    execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx]
  pins
  exec_simp
  have hb31 : (n != 31) = true := by simp; omega
  simp only [choice_unit] at hm
  have hel0 : (3#2 != EL0) = true := by decide
  have hpf : (MemOp.MemOp_LOAD != MemOp.MemOp_PREFETCH) = true := by decide
  simp only [sz8, sz8', w64, hb31, hel0, hpf, Bool.and_true, BitVec.setWidth_eq]
  esimp
  simp only [sz8', hm, BitVec.setWidth_eq]
  esimp

theorem str_exec {t n : Nat} (ht : t < 31) (hn : n < 31) (imm : BitVec 12) {a v : BitVec 64} (ha : xget s.regs n = some a)
    (hv : xget s.regs t = some v) (hlt : VaOK (a + imm.setWidth 64 <<< 3).toNat)
    (hal : (a + imm.setWidth 64 <<< 3).toNat % 8 = 0) :
    decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned (BitVec.ofNat 5 t) (BitVec.ofNat 5 n) imm 0#2 3#2 s =
      .ok () { s with regs := s.regs.insert .InGuardedPage false, mem := wrD s.mem (a + imm.setWidth 64 <<< 3).toNat v } := by
  idx t; idx n
  have hg := gpr_ok hc .MemOp_STORE (.inr rfl)
  have hm := memsetG8 hc (a + imm.setWidth 64 <<< 3) v hlt hal
  have := u_MemOp; have := u_Constraint; have := read_gpr_ok ha; have := read_gpr_ok hv
  have hn31 : (n == 31) = false := by simp; omega
  have hspe : (s.regs.insert .InGuardedPage false).get? .SPESampleInFlight = some false := by
    simp [Std.ExtDHashMap.get?_insert]; exact hc.spe
  simp only [decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned,
    execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx]
  pins
  exec_simp
  have hb31 : (n != 31) = true := by simp; omega
  simp only [choice_unit] at hm
  have hel0 : (3#2 != EL0) = true := by decide
  have hpf : (MemOp.MemOp_STORE != MemOp.MemOp_PREFETCH) = true := by decide
  simp only [sz8, sz8', w64, hb31, hel0, hpf, Bool.and_true, BitVec.setWidth_eq]
  esimp
  simp only [sz8', hm, BitVec.setWidth_eq]
  esimp

theorem stur_exec {t n : Nat} (ht : t < 31) (hn : n < 31) (imm : BitVec 9) {a v : BitVec 64} (ha : xget s.regs n = some a)
    (hv : xget s.regs t = some v) (hlt : VaOK (a + imm.signExtend 64).toNat)
    (hal : (a + imm.signExtend 64).toNat % 8 = 0) :
    decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (BitVec.ofNat 5 t) (BitVec.ofNat 5 n) imm 0#2 3#2 s =
      .ok () { s with regs := s.regs.insert .InGuardedPage false, mem := wrD s.mem (a + imm.signExtend 64).toNat v } := by
  idx t; idx n
  have hg := gpr_ok hc .MemOp_STORE (.inr rfl)
  have hm := memsetG8 hc (a + imm.signExtend 64) v hlt hal
  have := u_MemOp; have := u_Constraint; have := read_gpr_ok ha; have := read_gpr_ok hv
  have hn31 : (n == 31) = false := by simp; omega
  have hspe : (s.regs.insert .InGuardedPage false).get? .SPESampleInFlight = some false := by
    simp [Std.ExtDHashMap.get?_insert]; exact hc.spe
  simp only [decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal, sign_extend, Sail.BitVec.signExtend]
  pins
  exec_simp
  have hb31 : (n != 31) = true := by simp; omega
  simp only [choice_unit] at hm
  have hel0 : (3#2 != EL0) = true := by decide
  have hpf : (MemOp.MemOp_STORE != MemOp.MemOp_PREFETCH) = true := by decide
  simp only [sz8, sz8', w64, hb31, hel0, hpf, Bool.and_true, BitVec.setWidth_eq]
  esimp
  simp only [sz8', hm, BitVec.setWidth_eq]
  esimp

end

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
  (heret : BitVec.ofNat 20 (w.toNat >>> 12) ≠ 879088#20)
include hf ha hpc hlt hal hm heret

theorem s0_igp : (s0of s w).regs.get? .InGuardedPage = some false := by simp [s0of, preRegs, Std.ExtDHashMap.get?_insert]

/-- full step for a load: `X[d] := v`, `InGuardedPage := false` (already false), memory unchanged -/
theorem full_ld {k : Int} {d : Nat} (hd : d < 31) {v : BitVec 64}
    (hdec : __DecodeA64 pc.toNat w (s0of s w) = .ok () { s0of s w with regs := xset (((s0of s w).regs.insert .SEE k).insert .InGuardedPage false) d v }) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX d v) ∧ ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧
      s'.mem = s.mem := by
  obtain ⟨b0, hb0, hbr0⟩ := hf.bt
  have hx : ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .SEE →
      (xset (((s0of s w).regs.insert .SEE k).insert .InGuardedPage false) d v).get? r = (s0of s w).regs.get? r := fun r h1 h2 => by
    rw [xset_get_ne _ _ _ _ h1]
    by_cases e : r = .InGuardedPage
    · subst e; simp [Std.ExtDHashMap.get?_insert]; exact (s0_igp hf ha hpc hlt hal hm heret).symm
    · simp [Std.ExtDHashMap.get?_insert, Ne.symm h2, Ne.symm e]
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm heret hdec (bt := false) (pc1 := pc) (b := b0)
    (fun r h1 h2 h3 _ _ _ _ => hx r h1 h3)
    (fun p hp => ⟨p, by rw [hx _ (xreg_ne' (by decide)) (by decide)]; exact s0_ps hf ha hpc hlt hal hm heret p hp, pkeep_refl p⟩)
    (by rw [hx _ (xreg_ne' (by decide)) (by decide)]; simp [s0of, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [hx _ (xreg_ne' (by decide)) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hpc)
    (by rw [hx _ (xreg_ne' (by decide)) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hb0) hbr0
    (by rw [hx _ (xreg_ne' (by decide)) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hf.btn)
    (Abs.xset (abs_ins (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) k) .InGuardedPage (by decide) (by decide) false) hd v)
  exact ⟨s', h1, h2, h3, by simpa using h4, h5⟩

/-- full step for a store: memory := `M`, `InGuardedPage := false` (already false), registers unchanged -/
theorem full_st {k : Int} {M : Std.ExtHashMap Nat (BitVec 8)}
    (hdec : __DecodeA64 pc.toNat w (s0of s w) = .ok () { s0of s w with regs := ((s0of s w).regs.insert .SEE k).insert .InGuardedPage false, mem := M }) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = M := by
  obtain ⟨b0, hb0, hbr0⟩ := hf.bt
  have hx : ∀ r : Register, r ≠ .SEE →
      (((s0of s w).regs.insert .SEE k).insert .InGuardedPage false).get? r = (s0of s w).regs.get? r := fun r h2 => by
    by_cases e : r = .InGuardedPage
    · subst e; simp [Std.ExtDHashMap.get?_insert]; exact (s0_igp hf ha hpc hlt hal hm heret).symm
    · simp [Std.ExtDHashMap.get?_insert, Ne.symm h2, Ne.symm e]
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm heret hdec (bt := false) (pc1 := pc) (b := b0)
    (fun r _ _ h3 _ _ _ _ => hx r h3)
    (fun p hp => ⟨p, by rw [hx _ (by decide)]; exact s0_ps hf ha hpc hlt hal hm heret p hp, pkeep_refl p⟩)
    (by rw [hx _ (by decide)]; simp [s0of, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [hx _ (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hpc)
    (by rw [hx _ (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hb0) hbr0
    (by rw [hx _ (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hf.btn)
    ((fun h => ⟨h.1, h.2⟩) (abs_ins (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) k) .InGuardedPage (by decide) (by decide) false))
  exact ⟨s', h1, h2, h3, by simpa using h4, h5⟩

end

theorem s0_mem (s : St) (w : BitVec 32) (k : Int) : ({ s0of s w with regs := (s0of s w).regs.insert .SEE k } : St).mem = s.mem := rfl

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`ldrb wt, [xn, #imm12]`** (`t n < 31`, address below `2^29`) -/
theorem full_ldrb (hK : w &&& 0xFFC00000#32 = 0x39400000#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn : (Sail.BitVec.slice w 5 5).toNat < 31) {b : BitVec 8}
    (hA : VaOK (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64).toNat)
    (hb : s.mem.get? (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64).toNat = some b) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (b.setWidth 64)) ∧ ArmFullB s' nb ∧
      s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_ldrbsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ldrb_exec (s := { s0of s w with regs := (s0of s w).regs.insert .SEE (633 : Int) }) (s0_pins' hf w _) ht hn _ (s0_xk ha w _ hn) hA hb] at hd
  exact full_ld hf ha hpc hlt hal hm (noteret hK 31 (by decide) (by decide) (by decide)) ht hd

/-- **`strb wt, [xn, #imm12]`** -/
theorem full_strb (hK : w &&& 0xFFC00000#32 = 0x39000000#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn : (Sail.BitVec.slice w 5 5).toNat < 31)
    (hA : VaOK (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64).toNat) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧
      s'.mem = s.mem.insert (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64).toNat
        ((a.x (Sail.BitVec.slice w 0 5).toNat).setWidth 8) := by
  have hd := dec_strbsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    strb_exec (s := { s0of s w with regs := (s0of s w).regs.insert .SEE (651 : Int) }) (s0_pins' hf w _) ht hn _ (s0_xk ha w _ hn) (s0_xk ha w _ ht) hA] at hd
  exact full_st hf ha hpc hlt hal hm (noteret hK 31 (by decide) (by decide) (by decide)) hd

/-- **`ldr xt, [xn, #8*imm12]`** (aligned) -/
theorem full_ldr (hK : w &&& 0xFFC00000#32 = 0xF9400000#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn : (Sail.BitVec.slice w 5 5).toNat < 31) {v : BitVec 64}
    (hA : VaOK (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64 <<< 3).toNat)
    (hA8 : (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64 <<< 3).toNat % 8 = 0)
    (hv : MemD s.mem (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64 <<< 3).toNat v) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat v) ∧ ArmFullB s' nb ∧
      s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_ldrsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ldr_exec (s := { s0of s w with regs := (s0of s w).regs.insert .SEE (630 : Int) }) (s0_pins' hf w _) ht hn _ (s0_xk ha w _ hn) hA hA8 hv] at hd
  exact full_ld hf ha hpc hlt hal hm (noteret hK 29 (by decide) (by decide) (by decide)) ht hd

/-- **`str xt, [xn, #8*imm12]`** (aligned) -/
theorem full_str (hK : w &&& 0xFFC00000#32 = 0xF9000000#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn : (Sail.BitVec.slice w 5 5).toNat < 31)
    (hA : VaOK (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64 <<< 3).toNat)
    (hA8 : (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64 <<< 3).toNat % 8 = 0) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧
      s'.mem = wrD s.mem (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64 <<< 3).toNat
        (a.x (Sail.BitVec.slice w 0 5).toNat) := by
  have hd := dec_strsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    str_exec (s := { s0of s w with regs := (s0of s w).regs.insert .SEE (648 : Int) }) (s0_pins' hf w _) ht hn _ (s0_xk ha w _ hn) (s0_xk ha w _ ht) hA hA8] at hd
  exact full_st hf ha hpc hlt hal hm (noteret hK 29 (by decide) (by decide) (by decide)) hd

/-- **`stur xt, [xn, #simm9]`** (aligned) -/
theorem full_stur (hK : w &&& 0xFFE00C00#32 = 0xF8000000#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn : (Sail.BitVec.slice w 5 5).toNat < 31)
    (hA : VaOK (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 12 9).signExtend 64).toNat)
    (hA8 : (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 12 9).signExtend 64).toNat % 8 = 0) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧
      s'.mem = wrD s.mem (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 12 9).signExtend 64).toNat
        (a.x (Sail.BitVec.slice w 0 5).toNat) := by
  have hd := dec_stursym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    stur_exec (s := { s0of s w with regs := (s0of s w).regs.insert .SEE (687 : Int) }) (s0_pins' hf w _) ht hn _ (s0_xk ha w _ hn) (s0_xk ha w _ ht) hA hA8] at hd
  exact full_st hf ha hpc hlt hal hm (noteret hK 29 (by decide) (by decide) (by decide)) hd

end
end ArmProof
