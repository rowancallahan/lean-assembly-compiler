/- L4 (partial): `ret` (`0xD65F03C0`) at the decode+execute layer, under an explicit EL1/EL3 configuration. -/
import Arm.Exec
import Proven.CompilerArm
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace ArmProof

/-- What `ret` needs: AArch64 state (`nRW = 0`) at EL1 or EL3; GCS, BRBE, SPE, PAuth and VHE not implemented;
AArch64 implemented at EL0 (this short-circuits `HaveAArch64`); SCR_EL3 present; no top-byte-ignore for the
current regime (`TCR_EL3.TBI = 0` at EL3, `TCR_EL1.TBI0 = TBI1 = 0` at EL1). -/
structure RetCfg (s : St) : Prop where
  p : ∃ p : ProcState, s.regs.get? .PSTATE = some p ∧ p.nRW = 0#1 ∧
    ((p.EL = 3#2 ∧ ∃ tcr : BitVec 64, s.regs.get? .TCR_EL3 = some tcr ∧ tcr.extractLsb 20 20 = 0#1) ∨
     p.EL = 1#2 ∧ ∃ tcr : BitVec 64, s.regs.get? .TCR_EL1 = some tcr ∧ tcr.extractLsb 37 37 = 0#1 ∧ tcr.extractLsb 38 38 = 0#1)
  fi : ∃ fi : Vector Bool 259, s.regs.get? .FeatureImpl = some fi ∧
    fi[num_of_Feature .FEAT_GCS]'(by decide) = false ∧ fi[num_of_Feature .FEAT_BRBE]'(by decide) = false ∧
    fi[num_of_Feature .FEAT_SPE]'(by decide) = false ∧ fi[num_of_Feature .FEAT_PAuth]'(by decide) = false ∧
    fi[num_of_Feature .FEAT_VHE]'(by decide) = false ∧ fi[num_of_Feature .FEAT_AA64EL0]'(by decide) = true
  scr : ∃ scr : BitVec 64, s.regs.get? .SCR_EL3 = some scr

theorem extract_full (t : BitVec 64) : BitVec.extractLsb 63 0 t = t := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb, BitVec.extractLsb']

theorem ret_beq : (BranchType.BranchType_RET == BranchType.BranchType_RET) = true := rfl

theorem dec_ret (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) :
    __DecodeA64 pc 0xD65F03C0#32 s = decode_ret_aarch64_instrs_branch_unconditional_register 0#5 30#5 0#1 0#1 2#2 0#1
      { s with regs := s.regs.insert .SEE (94 : Int) } := by
  have hk : ∀ k : Int, 1 ≤ k → see < k := fun k hk => by omega
  simp (config := {decide := true}) [__DecodeA64, __DecodeA64_BranchExcSys, andM, ToBool.toBool, BitVec.slice, PreSail.readReg,
    PreSail.writeReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, h, hs, hk, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']

syntax "ret_simp" : tactic
macro_rules | `(tactic| ret_simp) => `(tactic| simp (config := {decide := true}) [*, X_read, get_R, execute_aarch64_instrs_branch_unconditional_register, BranchTo,
    Hint_Branch, HaveGCS, HaveBRBExt, HaveStatisticalProfiling, IsFeatureImplemented, undefined_BranchType,
    undefined_GCSInstruction, AArch64_BranchAddr, AddrTop, S1TranslationRegime, ELUsingAArch32, ELStateUsingAArch32,
    ELStateUsingAArch32K, IsSecureBelowEL3, SCR_GEN_read, EffectiveTBI, UsingAArch32, HaveAArch64, HaveEL, HaveAArch32,
    HaveAArch32EL, HavePACExt, HaveVirtHostExt, _get_TCR_EL3_Type_TBI, _get_TCR_EL1_Type_TBI0, _get_TCR_EL1_Type_TBI1, _get_SCRType_NS, Mk_SCRType, EL3, EL2, EL1, EL0,
    __UNKNOWN_boolean, PreSail.undefined_bitvector, PreSail.undefined_bool, PreSail.internal_pick, PreSail.sail_assert,
    choose_ok, PreSail.readReg, PreSail.writeReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, Sail.BitVec.extractLsb,
    Sail.BitVec.zeroExtend, BitVec.extractLsb', extract_full, read_gpr_get, andM, orM, ToBool.toBool, ret_beq,
    Sail.BitVec.length, Std.ExtDHashMap.get?_insert])

theorem ret_exec (s : St) (hc : RetCfg s) {t : BitVec 64} (h30 : xget s.regs 30 = some t) :
    decode_ret_aarch64_instrs_branch_unconditional_register 0#5 30#5 0#1 0#1 2#2 0#1 s = .ok ()
      { s with regs := (((s.regs.insert .BTypeNext 0#2).insert .Branchtypetaken .BranchType_RET).insert ._PC t).insert .__BranchTaken true } := by
  obtain ⟨p, hp, hrw, hel⟩ := hc.p
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hc.fi
  obtain ⟨scr, hscr⟩ := hc.scr
  dsimp only [decode_ret_aarch64_instrs_branch_unconditional_register]; dsimp
  cases hel with
  | inl h => obtain ⟨hel3, tcr, htcr, htbi⟩ := h; ret_simp
  | inr h =>
    obtain ⟨hel1, tcr, htcr, htbi0, htbi1⟩ := h
    by_cases hb : BitVec.join1 [BitVec.access (BitVec.extractLsb 63 0 t) 55] = 1#1 <;> ret_simp


/-- **L4 (ret, decode+execute)**: under `RetCfg`, the backend's `ret` word sets `_PC := X30` (and the branch
bookkeeping registers BTypeNext, Branchtypetaken, __BranchTaken), nothing else besides SEE. -/
theorem ret_word (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) (hc : RetCfg s)
    {t : BitVec 64} (h30 : xget s.regs 30 = some t) :
    __DecodeA64 pc Proven.Arm.iRet s = .ok ()
      { s with regs := ((((s.regs.insert .SEE (94 : Int)).insert .BTypeNext 0#2).insert .Branchtypetaken .BranchType_RET).insert ._PC t).insert .__BranchTaken true } := by
  rw [show Proven.Arm.iRet = 0xD65F03C0#32 from rfl, dec_ret s pc see hs h]
  obtain ⟨p, hp, hrw, hel⟩ := hc.p
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hc.fi
  obtain ⟨scr, hscr⟩ := hc.scr
  exact ret_exec { s with regs := s.regs.insert .SEE (94 : Int) } ⟨⟨p, by simp [Std.ExtDHashMap.get?_insert, hp], hrw,
      by simpa [Std.ExtDHashMap.get?_insert] using hel⟩,
    ⟨fi, by simp [Std.ExtDHashMap.get?_insert, hfi], hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩,
    ⟨scr, by simp [Std.ExtDHashMap.get?_insert, hscr]⟩⟩
    ((xget_insert _ .SEE _ (by decide) 30).trans h30)

end ArmProof
