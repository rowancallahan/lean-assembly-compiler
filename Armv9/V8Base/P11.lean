import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.ReverseEndianness
import Armv9.Option
import Armv9.MonoRewrites
import Armv9.Common
import Armv9.Prelude
import Armv9.Builtins
import Armv9Core.V8Base
import Armv9.V8Base.P00
import Armv9.V8Base.P01
import Armv9.V8Base.P02
import Armv9.V8Base.P04
import Armv9.V8Base.P05
import Armv9.V8Base.P06
import Armv9.V8Base.P07
import Armv9.V8Base.P08
import Armv9.V8Base.P09
import Armv9.V8Base.P10

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

-- https://github.com/leanprover/lean4/issues/13858
-- https://github.com/leanprover/lean4/issues/15685
set_option backward.do.legacy true

-- https://github.com/leanprover/lean4/issues/15661
set_option cleanup.letToHave false

open Sail
open Sail.ConcurrencyInterfaceV1

noncomputable section
namespace Armv9

open ConcurrencyInterfaceV1

namespace Functions

open signal
open option
open exception
open arm_acc_type
open __InstrEnc
open WFxType
open VFPNegMul
open VCGTtype
open VCGEType
open VBitOps
open VBitOp
open VARange
open Unpredictable
open TranslationStage
open TimeStamp
open TMFailure
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open SystemHintOp
open Signal
open ShiftType
open Shareability
open SecurityState
open SVECmp
open SRType
open SMEExceptionType
open SDFType
open RestrictType
open Register
open Regime
open ReduceOp
open PrivilegeLevel
open PrefetchHint
open PSTATEField
open PGSe
open PASpace
open PARTIDspaceType
open OpType
open MoveWideOp
open MemType
open MemTagType
open MemOp
open MemAtomicOp
open MOPSStage
open MBReqTypes
open MBReqDomain
open LogicalOp
open InterruptID
open InstrSet
open ImmediateOp
open GPCF
open GCSInstruction
open Feature
open Fault
open FPUnaryOp
open FPType
open FPRounding
open FPMaxMinOp
open FPExc
open FPConvOp
open ExtendType
open ExceptionalOccurrenceTargetState
open Exception
open ErrorState
open DeviceType
open DescriptorType
open DSBAlias
open CrossTriggerIn
open CountOp
open Constraint
open CompareOp
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open BranchType
open Barrier
open ArchVersion
open AccessType
open ATAccess

/-- Type quantifiers: k_cold : Bool -/
def ResetControlRegisters (cold : Bool) : SailM Unit := do
  if ((← (HaveAArch64 ())) : Bool)
  then (AArch64_AutoGen_ArchitectureReset cold)
  else (AArch32_AutoGen_ArchitectureReset cold)
  (AArch32_IMPDEFResets ())
  (AArch64_IMPDEFResets ())
  (__Reset cold)

def AArch64_CheckFPEnabled (_ : Unit) : SailM Unit := do
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
       (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
       (pure (! (← (IsInHost ()))))))) : Bool)
  then
    (do
      let disabled ← (( do (undefined_bool ()) ) : SailM Bool )
      let disabled ← (( do
        let b__0 ← do (pure (_get_CPACR_EL1_Type_FPEN (← readReg CPACR_EL1)))
        if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
        then (pure true)
        else
          (do
            if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
            then (do (pure ((← readReg PSTATE).EL == EL0)))
            else (pure false)) ) : SailM Bool )
      let disabled := disabled
      if (disabled : Bool)
      then (AArch64_AdvSIMDFPAccessTrap EL1)
      else (pure ()))
  else (pure ())
  (AArch64_CheckFPAdvSIMDTrap ())

/-- Type quantifiers: CRm : Int, CRn : Int, nreg : Int -/
def AArch64_CheckCP15InstrCoarseTraps (CRn : Int) (nreg : Int) (CRm : Int) : SailM Unit := do
  let major ← (( do (undefined_int ()) ) : SailM Int )
  let trapped_encoding : Bool := ((((CRn == 9) && ((CRm == 0) || ((CRm == 1) || ((CRm == 2) || ((CRm == 5) || ((CRm == 6) || ((CRm == 7) || (CRm == 8)))))))) || ((CRn == 10) && ((CRm == 0) || ((CRm == 1) || ((CRm == 4) || (CRm == 8)))))) || ((CRn == 11) && ((CRm == 0) || ((CRm == 1) || ((CRm == 2) || ((CRm == 3) || ((CRm == 4) || ((CRm == 5) || ((CRm == 6) || ((CRm == 7) || ((CRm == 8) || (CRm == 15))))))))))))
  if (((←((HaveFeatTIDCP1 ()) <&&> (do
         (pure ((← readReg PSTATE).EL == EL0))) <&&> (do
         (pure (! (← (IsInHost ()))))) <&&> (do
         (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
         (pure ((_get_SCTLR_EL1_Type_TIDCP (← readReg SCTLR_EL1)) == 1#1))))) && trapped_encoding) : Bool)
  then
    (do
      if ((←((EL2Enabled ()) <&&> (do
           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x3#4))
      else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x3#4)))
  else (pure ())
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
       (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
       (EL2Enabled ())))) : Bool)
  then
    (do
      if (((←((HaveFeatTIDCP1 ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL0))) <&&> (do
             (IsInHost ())) <&&> (do
             (pure ((_get_SCTLR_EL2_Type_TIDCP (← readReg SCTLR_EL2)) == 1#1))))) && trapped_encoding) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x3#4))
      else (pure ())
      let major :=
        if ((nreg == 1) : Bool)
        then CRn
        else CRm
      sail_assert ((0 ≤b major) && (major <b 64)) "src/v8_base.sail:34133.54-34133.55"
      if ((←((pure ((! (← (IsInHost ()))) && (! ((major == 4) || (major == 14))))) <&&> (do
           (pure ((BitVec.join1 [(BitVec.access (← readReg HSTR_EL2) major)]) == 1#1))) <||> (do
           (pure ((((_get_HCR_EL2_Type_TIDCP (← readReg HCR_EL2)) == 1#1) && (nreg == 1)) && trapped_encoding))))) : Bool)
      then
        (do
          if ((←((pure ((← readReg PSTATE).EL == EL0)) <&&> (do
               (__IMPDEF_boolean "UNDEF unallocated CP15 access at EL0")))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (pure ())
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x3#4)))
      else (pure ()))
  else (pure ())

def SPEResetSampleCounter (_ : Unit) : SailM Unit := do
  writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSICR_EL1) 31 0 (Sail.BitVec.updateSubrange (Sail.BitVec.extractLsb (← readReg PMSICR_EL1) 31 0) 31 8 (_get_PMSIRR_EL1_Type_INTERVAL (← readReg PMSIRR_EL1))))
  if ((←((pure ((_get_PMSIRR_EL1_Type_RND (← readReg PMSIRR_EL1)) == 1#1)) <&&> (do
       (pure ((_get_PMSIDR_EL1_Type_ERnd (← readReg PMSIDR_EL1)) == 0#1))))) : Bool)
  then writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSICR_EL1) 31 0 (Sail.BitVec.updateSubrange (Sail.BitVec.extractLsb (← readReg PMSICR_EL1) 31 0) 7 0 (← (SPEGetRandomInterval ()))))
  else writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSICR_EL1) 31 0 (Sail.BitVec.updateSubrange (Sail.BitVec.extractLsb (← readReg PMSICR_EL1) 31 0) 7 0 (Zeros (n := 8))))

def SPEPostExecution (_ : Unit) : SailM Unit := do
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      writeReg SPESampleInFlight false
      (PMUEvent PMU_EVENT_SAMPLE_FEED)
      let loop_counter_index_lower := 0
      let loop_counter_index_upper := (SPEMaxCounters -i 1)
      let mut loop_vars := ()
      for counter_index in [loop_counter_index_lower:loop_counter_index_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          if ((GetElem?.getElem! (← readReg SPESampleCounterPending) counter_index) : Bool)
          then (SPEStopCounter counter_index)
          else (pure ())
      (pure loop_vars)
      let discard : Bool := false
      let discard ← (( do
        if ((← (HaveStatisticalProfilingv1p2 ())) : Bool)
        then (do (pure ((_get_PMBLIMITR_EL1_Type_FM (← readReg PMBLIMITR_EL1)) == 0b10#2)))
        else (pure discard) ) : SailM Bool )
      if (((← (SPECollectRecord (← readReg SPESampleEvents) (GetElem?.getElem! (← readReg SPESampleCounter) SPECounterPosTotalLatency) (← readReg SPESampleOpType))) && (! discard)) : Bool)
      then
        (do
          (SPEConstructRecord ())
          if ((← (SPEBufferIsFull ())) : Bool)
          then (SPEBufferFilled ())
          else (pure ()))
      else (pure ())
      (SPEResetSampleStorage ()))
  else (pure ())

def SPEGetRandomBoolean (_ : Unit) : SailM Bool := do
  (pure ((BitVec.join1 [(BitVec.access (← (SPEGetRandomInterval ())) 0)]) == 1#1))

def AArch64_ExceptionReturn (new_pc_in : (BitVec 64)) (spsr : (BitVec 64)) : SailM Unit := do
  let iesb_req ← (( do (undefined_bool ()) ) : SailM Bool )
  let sync_errors ← (( do (undefined_bool ()) ) : SailM Bool )
  let new_pc : (BitVec 64) := new_pc_in
  if ((←((HaveTME ()) <&&> (do
       (pure ((← readReg TSTATE).depth >b 0))))) : Bool)
  then (FailTransaction TMFailure_ERR false)
  else (pure ())
  let sync_errors ← (( do
    if ((← (HaveIESB ())) : Bool)
    then
      (do
        let sync_errors ← (( do (pure ((_get_SCTLRType_IESB (← (SCTLR_read__1 ()))) == 1#1)) ) : SailM Bool )
        let sync_errors ← (( do
          if ((← (HaveDoubleFaultExt ())) : Bool)
          then (do (pure sync_errors) <||> (do (pure (((_get_SCR_EL3_Type_EA (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_NMEA (← readReg SCR_EL3))) == 0b11#2)) <&&> (do (pure ((← readReg PSTATE).EL == EL3)))))
          else (pure sync_errors) ) : SailM Bool )
        if (sync_errors : Bool)
        then
          (do
            let _ : Unit := (SynchronizeErrors ())
            let iesb_req : Bool := true
            (TakeUnmaskedPhysicalSErrorInterrupts iesb_req))
        else (pure ())
        (pure sync_errors))
    else (pure sync_errors) ) : SailM Bool )
  let sync_errors := sync_errors
  let _ : Unit := (SynchronizeContext ())
  writeReg __InstructionStep false
  let source_el ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let illegal_psr_state ← (( do (IllegalExceptionReturn spsr) ) : SailM Bool )
  (SetPSTATEFromPSR__1 spsr illegal_psr_state)
  let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
  (SendEventLocal ())
  let new_pc ← (( do
    if ((illegal_psr_state && ((BitVec.join1 [(BitVec.access spsr 4)]) == 1#1)) : Bool)
    then
      (do
        let new_pc ← (pure (Sail.BitVec.updateSubrange new_pc 63 32 (← (__UNKNOWN_bits 32))))
        (pure (Sail.BitVec.updateSubrange new_pc 1 0 (← (__UNKNOWN_bits 2)))))
    else
      (do
        if ((← (UsingAArch32 ())) : Bool)
        then
          (do
            if (((← readReg PSTATE).T == 1#1) : Bool)
            then (pure (BitVec.update new_pc 0 (Bit 0#1)))
            else (pure (Sail.BitVec.updateSubrange new_pc 1 0 0b00#2)))
        else (do (AArch64_BranchAddr new_pc (← readReg PSTATE).EL))) ) : SailM (BitVec 64) )
  if ((← (HaveBRBExt ())) : Bool)
  then (BRBEExceptionReturn new_pc source_el)
  else (pure ())
  if ((← (UsingAArch32 ())) : Bool)
  then
    (do
      if ((←((HaveSME ()) <&&> (do
           (pure ((← readReg PSTATE).SM == 1#1))))) : Bool)
      then (ResetSVEState ())
      else (pure ())
      let branch_conditional : Bool := false
      (BranchTo (Sail.BitVec.extractLsb new_pc 31 0) BranchType_ERET branch_conditional))
  else (BranchToAddr new_pc BranchType_ERET)
  (CheckExceptionCatch false)

def AArch64_AT (address : (BitVec 64)) (stage_in : TranslationStage) (el_in : (BitVec 2)) (ataccess : ATAccess) : SailM Unit := do
  let stage : TranslationStage := stage_in
  let el : (BitVec 2) := el_in
  let effective_nse_ns ← (( do (pure ((← (EffectiveSCR_EL3_NSE ())) +++ (← (EffectiveSCR_EL3_NS ())))) ) : SailM (BitVec 2) )
  if ((((←((HaveRME ()) <&&> (do
           (pure ((← readReg PSTATE).EL == EL3))))) && (effective_nse_ns == 0b10#2)) && (el != EL3)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let el ← (( do
    if ((((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) && (el == EL1)) && (BEq.beq stage TranslationStage_1)) : Bool)
    then (pure EL2)
    else (pure el) ) : SailM (BitVec 2) )
  let stage ← (( do
    if ((←((pure ((HaveEL EL3) && (BEq.beq stage TranslationStage_12))) <&&> (do
         (pure (! (← (EL2Enabled ()))))))) : Bool)
    then (pure TranslationStage_1)
    else (pure stage) ) : SailM TranslationStage )
  let write : Bool := ((BEq.beq ataccess ATAccess_WritePAN) || (BEq.beq ataccess ATAccess_Write))
  let ss ← (( do (SecurityStateAtEL el) ) : SailM SecurityState )
  let pan : Bool := ((BEq.beq ataccess ATAccess_ReadPAN) || (BEq.beq ataccess ATAccess_WritePAN))
  let accdesc ← (( do (CreateAccDescAT ss el write pan) ) : SailM AccessDescriptor )
  let aligned : Bool := true
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let regime ← (( do (undefined_Regime ()) ) : SailM Regime )
  let regime ← (( do
    if ((BEq.beq stage TranslationStage_12) : Bool)
    then (pure Regime_EL10)
    else (do (TranslationRegime el)) ) : SailM Regime )
  let addrdesc ← (( do (undefined_AddressDescriptor ()) ) : SailM AddressDescriptor )
  let (addrdesc, fault) ← (( do
    if ((←((pure (el == EL0)) <&&> (do
         (ELUsingAArch32 EL1)) <||> (do
         (pure (el != EL0)) <&&> (do
           (ELUsingAArch32 el))))) : Bool)
    then
      (do
        let tsi ← do (AArch32_GetTranslationStartInfo regime ss accdesc (Sail.BitVec.extractLsb address 31 0) 1)
        (start_translation tsi)
        let (addrdesc, fault) ← (( do
          if ((←((pure (BEq.beq regime Regime_EL2)) <||> (do
               (pure ((_get_TTBCR_Type_EAE (← (TTBCR_read ()))) == 1#1))))) : Bool)
          then
            (do
              let (tup__0, tup__1) ← do (AArch32_S1TranslateLD fault regime (Sail.BitVec.extractLsb address 31 0) aligned accdesc)
              let fault : FaultRecord := tup__0
              let addrdesc : AddressDescriptor := tup__1
              (pure (addrdesc, fault)))
          else
            (do
              let (__tup_0, __tup_1, _) ← do (AArch32_S1TranslateSD fault regime (Sail.BitVec.extractLsb address 31 0) aligned accdesc)
              let fault : FaultRecord := __tup_0
              let addrdesc : AddressDescriptor := __tup_1
              (pure (addrdesc, fault))) ) : SailM (AddressDescriptor × FaultRecord) )
        (pure (addrdesc, fault)))
    else
      (do
        let tsi ← do (AArch64_GetTranslationStartInfo regime ss accdesc address 1)
        (start_translation tsi)
        let (tup__0, tup__1) ← do (AArch64_S1Translate fault regime address aligned accdesc)
        let fault : FaultRecord := tup__0
        let addrdesc : AddressDescriptor := tup__1
        (pure (addrdesc, fault))) ) : SailM (AddressDescriptor × FaultRecord) )
  let (addrdesc, fault) ← (( do
    if (((BEq.beq stage TranslationStage_12) && (BEq.beq fault.statuscode Fault_None)) : Bool)
    then
      (do
        let s1aarch64 ← (( do (undefined_bool ()) ) : SailM Bool )
        let (addrdesc, fault) ← (( do
          if ((←((pure ((← (ELUsingAArch32 EL1)) && (BEq.beq regime Regime_EL10))) <&&> (do
               (EL2Enabled ())))) : Bool)
          then
            (do
              let addrdesc : AddressDescriptor := { addrdesc with vaddress := (Sail.BitVec.zeroExtend address 64) }
              let (tup__0, tup__1) ← do (AArch32_S2Translate fault addrdesc none aligned accdesc)
              let fault : FaultRecord := tup__0
              let addrdesc : AddressDescriptor := tup__1
              (pure (addrdesc, fault)))
          else
            (do
              let (addrdesc, fault) ← (( do
                if ((←((pure (BEq.beq regime Regime_EL10)) <&&> (do
                     (EL2Enabled ())))) : Bool)
                then
                  (do
                    let s1aarch64 : Bool := true
                    let (tup__0, tup__1) ← do (AArch64_S2Translate fault addrdesc s1aarch64 none aligned accdesc)
                    let fault : FaultRecord := tup__0
                    let addrdesc : AddressDescriptor := tup__1
                    (pure (addrdesc, fault)))
                else (pure (addrdesc, fault)) ) : SailM (AddressDescriptor × FaultRecord) )
              (pure (addrdesc, fault))) ) : SailM (AddressDescriptor × FaultRecord) )
        (pure (addrdesc, fault)))
    else (pure (addrdesc, fault)) ) : SailM (AddressDescriptor × FaultRecord) )
  let is_ATS1Ex : Bool := (bne stage TranslationStage_12)
  let addrdesc ← (( do
    if ((bne fault.statuscode Fault_None) : Bool)
    then
      (do
        let addrdesc ← (CreateFaultyAddressDescriptor address fault)
        if ((←((IsExternalAbort__1 fault) <||> (do
             (pure (((← readReg PSTATE).EL == EL1) && fault.s2fs1walk))) <||> (do
             (pure ((← (HaveRME ())) && (bne fault.gpcf.gpf GPCF_None))) <&&> (do
               (ReportAsGPCException fault) <||> (do
                 (pure (((←((pure ((_get_HCR_EL2_Type_GPF (← readReg HCR_EL2)) == 1#1)) <&&> (do (pure ((← readReg PSTATE).EL == EL1))))) && ((el == EL1) || (el == EL0))) && is_ATS1Ex))))))) : Bool)
        then
          (do
            (PAR_EL1_write (Mk_PAR_EL1_Type (← (__UNKNOWN_bits 128))))
            (AArch64_Abort address addrdesc.fault))
        else (pure ())
        (pure addrdesc))
    else (pure addrdesc) ) : SailM AddressDescriptor )
  let addrdesc := addrdesc
  (end_translation addrdesc)
  (AArch64_EncodePAR regime is_ATS1Ex addrdesc)

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV85 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap5_IMPLEMENTED enabled
  if (enabled : Bool)
  then (__ConfigureV84 enabled)
  else (pure ())

/-- Type quantifiers: k_advsimd : Bool -/
def AArch32_CheckFPAdvSIMDTrap (advsimd : Bool) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  let hcptr_cp10 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let hcptr_tase ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let ss ← (( do (undefined_SecurityState ()) ) : SailM SecurityState )
  if ((←((EL2Enabled ()) <&&> (do
       (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
  then (AArch64_CheckFPAdvSIMDTrap ())
  else
    (do
      if ((←((pure (HaveEL EL3)) <&&> (do
           (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
           (pure ((_get_CPTR_EL3_Type_TFP (← readReg CPTR_EL3)) == 1#1))) <&&> (do
           (EL3SDDUndefPriority ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
      if (((HaveEL EL2) && (bne ss SS_Secure)) : Bool)
      then
        (do
          let hcptr_tase ← (( do (pure (_get_HCPTR_Type_TASE (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
          let hcptr_cp10 ← (( do (pure (_get_HCPTR_Type_TCP10 (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
          let (hcptr_cp10, hcptr_tase) ← (( do
            if ((←((pure (HaveEL EL3)) <&&> (do
                 (ELUsingAArch32 EL3)))) : Bool)
            then
              (do
                let hcptr_tase ← (( do
                  if (((_get_NSACR_Type_NSASEDIS (← readReg NSACR)) == 1#1) : Bool)
                  then (pure 1#1)
                  else (pure hcptr_tase) ) : SailM (BitVec 1) )
                let hcptr_cp10 ← (( do
                  if (((_get_NSACR_Type_cp10 (← readReg NSACR)) == 0#1) : Bool)
                  then (pure 1#1)
                  else (pure hcptr_cp10) ) : SailM (BitVec 1) )
                (pure (hcptr_cp10, hcptr_tase)))
            else (pure (hcptr_cp10, hcptr_tase)) ) : SailM ((BitVec 1) × (BitVec 1)) )
          if (((advsimd && (hcptr_tase == 1#1)) || (hcptr_cp10 == 1#1)) : Bool)
          then
            (do
              let except ← (( do (ExceptionSyndrome Exception_AdvSIMDFPAccessTrap) ) : SailM ExceptionRecord )
              let except ← (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 24 20 (← (ConditionSyndrome ()))))) })
              let except : ExceptionRecord :=
                if (advsimd : Bool)
                then { except with syndrome := (BitVec.update except.syndrome 5 (Bit 1#1)) }
                else
                  (let except : ExceptionRecord := { except with syndrome := (BitVec.update except.syndrome 5 (Bit 0#1)) }
                  { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 3 0 0b1010#4) })
              if (((← readReg PSTATE).EL == EL2) : Bool)
              then (AArch32_TakeUndefInstrException__1 except)
              else (AArch32_TakeHypTrapException__1 except))
          else (pure ()))
      else (pure ())
      if ((←((pure (HaveEL EL3)) <&&> (do
           (pure (! (← (ELUsingAArch32 EL3))))))) : Bool)
      then
        (do
          if (((_get_CPTR_EL3_Type_TFP (← readReg CPTR_EL3)) == 1#1) : Bool)
          then
            (do
              if ((← (EL3SDDUndef ())) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (AArch64_AdvSIMDFPAccessTrap EL3))
          else (pure ()))
      else (pure ()))

/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 -/
def MemA_set (address : (BitVec 32)) (size : Nat) (value_name : (BitVec (8 * size))) : SailM Unit := do
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_STORE acqrel tagchecked) ) : SailM AccessDescriptor )
  (Mem_with_type_set address size accdesc value_name)

/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 -/
def MemU_set (address : (BitVec 32)) (size : Nat) (value_name : (BitVec (8 * size))) : SailM Unit := do
  let nontemporal : Bool := false
  let privileged ← (( do (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescGPR MemOp_STORE nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  (Mem_with_type_set address size accdesc value_name)

/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 -/
def MemU_unpriv_set (address : (BitVec 32)) (size : Nat) (value_name : (BitVec (8 * size))) : SailM Unit := do
  let nontemporal : Bool := false
  let privileged : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescGPR MemOp_STORE nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  (Mem_with_type_set address size accdesc value_name)

/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 -/
def MemO_set (address : (BitVec 32)) (size : Nat) (value_name : (BitVec (8 * size))) : SailM Unit := do
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescAcqRel MemOp_STORE tagchecked) ) : SailM AccessDescriptor )
  (Mem_with_type_set address size accdesc value_name)

/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 -/
def MemS_set (address : (BitVec 32)) (size : Nat) (value_name : (BitVec (8 * size))) : SailM Unit := do
  let accdesc ← (( do (CreateAccDescA32LSMD MemOp_STORE) ) : SailM AccessDescriptor )
  (Mem_with_type_set address size accdesc value_name)

def AArch32_CheckAdvSIMDOrFPRegisterTraps (reg : (BitVec 4)) : SailM Unit := do
  let tid0 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let tid3 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  if ((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
       (EL2Enabled ())))) : Bool)
  then
    (do
      let tid0 ← (( do
        if ((← (ELUsingAArch32 EL2)) : Bool)
        then (pure (_get_HCR_Type_TID0 (← (HCR_read ()))))
        else (pure (_get_HCR_EL2_Type_TID0 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
      let tid3 ← (( do
        if ((← (ELUsingAArch32 EL2)) : Bool)
        then (pure (_get_HCR_Type_TID3 (← (HCR_read ()))))
        else (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
      if ((((tid0 == 1#1) && (reg == 0b0000#4)) || ((tid3 == 1#1) && ((reg == 0b0101#4) || ((reg == 0b0110#4) || (reg == 0b0111#4))))) : Bool)
      then
        (do
          if ((← (ELUsingAArch32 EL2)) : Bool)
          then (AArch32_SystemAccessTrap M32_Hyp (BitVec.toNat 0x8#4))
          else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x8#4)))
      else (pure ()))
  else (pure ())

def AArch32_CheckForWFxTrap (target_el : (BitVec 2)) (wfxtype : WFxType) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  sail_assert (HaveEL target_el) "src/v8_base.sail:43067.28-43067.29"
  if ((! (← (ELUsingAArch32 target_el))) : Bool)
  then (do (AArch64_CheckForWFxTrap target_el wfxtype))
  else
    (do
      let is_wfe : Bool := (BEq.beq wfxtype WFxType_WFE)
      let trap ← (( do (undefined_bool ()) ) : SailM Bool )
      let trap ← (( do
        let questionMark := target_el
        if ((questionMark == EL1) : Bool)
        then
          (do
            (pure ((← (do
                  if (is_wfe : Bool)
                  then (pure (_get_SCTLR_Type_nTWE (← (SCTLR_read__2 ()))))
                  else (pure (_get_SCTLR_Type_nTWI (← (SCTLR_read__2 ())))))) == 0#1)))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                (pure ((← (do
                      if (is_wfe : Bool)
                      then (pure (_get_HCR_Type_TWE (← (HCR_read ()))))
                      else (pure (_get_HCR_Type_TWI (← (HCR_read ())))))) == 1#1)))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    (pure ((← (do
                          if (is_wfe : Bool)
                          then (pure (_get_SCR_Type_TWE (← readReg SCR)))
                          else (pure (_get_SCR_Type_TWI (← readReg SCR))))) == 1#1)))
                else (pure trap))) ) : SailM Bool )
      if (trap : Bool)
      then
        (do
          if ((←((pure (target_el == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
               (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
          then (AArch64_WFxTrap wfxtype target_el)
          else (pure ())
          if ((target_el == EL3) : Bool)
          then (AArch32_TakeMonitorTrapException ())
          else
            (do
              if ((target_el == EL2) : Bool)
              then
                (do
                  let except ← (( do (ExceptionSyndrome Exception_WFxTrap) ) : SailM ExceptionRecord )
                  let except ← (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 24 20 (← (ConditionSyndrome ()))))) })
                  let except : ExceptionRecord :=
                    match wfxtype with
                    | .WFxType_WFI => { except with syndrome := (BitVec.update except.syndrome 0 (Bit 0#1)) }
                    | .WFxType_WFE => { except with syndrome := (BitVec.update except.syndrome 0 (Bit 1#1)) }
                    | _ => except
                  (AArch32_TakeHypTrapException__1 except))
              else (AArch32_TakeUndefInstrException ())))
      else (pure ()))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPRound__1 (op : real) (fpcr_in : (BitVec 64)) (rounding : FPRounding) (N : Nat) : SailM (BitVec N) := do
  let fpexc : Bool := true
  (FPRound__2 op fpcr_in rounding fpexc N)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPUnpack (fpval : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (FPType × (BitVec 1) × real) := do
  let fp_type ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  let fpexc : Bool := true
  let (fp_type, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpackBase fpval fpcr fpexc)
    let fp_type : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fp_type, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  (pure (fp_type, sign, value_name))

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPUnpack__1 (fpval : (BitVec k_N)) (fpcr_in : (BitVec 64)) (fpexc : Bool) : SailM (FPType × (BitVec 1) × real) := do
  let fp_type ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  let (fp_type, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpackBase fpval fpcr fpexc)
    let fp_type : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fp_type, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  (pure (fp_type, sign, value_name))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPProcessNaNs (type1 : FPType) (type2 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (Bool × (BitVec k_N)) := do
  let fpexc : Bool := true
  (FPProcessNaNs__1 type1 type2 op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPUnpackCV (fpval : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (FPType × (BitVec 1) × real) := do
  let fp_type ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 19 19 0#1)
  let fpexc : Bool := true
  let (fp_type, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpackBase fpval fpcr fpexc)
    let fp_type : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fp_type, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  (pure (fp_type, sign, value_name))

def CheckSVEEnabled (_ : Unit) : SailM Unit := do
  if ((←((HaveSME ()) <&&> (do
       (pure ((← readReg PSTATE).SM == 1#1))))) : Bool)
  then (CheckSMEEnabled ())
  else
    (do
      if ((←((HaveSME ()) <&&> (do
           (pure (! (← (HaveSVE ()))))))) : Bool)
      then (CheckStreamingSVEEnabled ())
      else (CheckOriginalSVEEnabled ()))

def CheckStreamingSVEAndZAEnabled (_ : Unit) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  if (((← readReg PSTATE).ZA == 0#1) : Bool)
  then (SMEAccessTrap SMEExceptionType_InactiveZA (← readReg PSTATE).EL)
  else (pure ())

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_isbfloat16 : Bool, k_N = 32 -/
def FPDot__1 (op1_a : (BitVec (k_N / 2))) (op1_b : (BitVec (k_N / 2))) (op2_a : (BitVec (k_N / 2))) (op2_b : (BitVec (k_N / 2))) (fpcr_in : (BitVec 64)) (isbfloat16 : Bool) (fpexc : Bool) : SailM (BitVec k_N) := do
  let infPa ← (( do (undefined_bool ()) ) : SailM Bool )
  let infPb ← (( do (undefined_bool ()) ) : SailM Bool )
  let invalidop ← (( do (undefined_bool ()) ) : SailM Bool )
  let result_sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign1_a ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign1_b ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2_a ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2_b ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let signPa ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let signPb ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1_a ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type1_b ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2_a ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2_b ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_a_name ← (( do (undefined_real ()) ) : SailM real )
  let value1_b_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_a_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_b_name ← (( do (undefined_real ()) ) : SailM real )
  let zeroPa ← (( do (undefined_bool ()) ) : SailM Bool )
  let zeroPb ← (( do (undefined_bool ()) ) : SailM Bool )
  let fpcr : FPCRType := fpcr_in
  sail_assert (SPEMaxCounters == 32) "src/v8_base.sail:32331.19-32331.20"
  let result ← (( do (undefined_bitvector SPEMaxCounters) ) : SailM (BitVec k_N) )
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let (sign1_a, type1_a, value1_a_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpackBase__1 op1_a fpcr fpexc isbfloat16)
    let type1_a : FPType := tup__0
    let sign1_a : (BitVec 1) := tup__1
    let value1_a_name : real := tup__2
    (pure (sign1_a, type1_a, value1_a_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign1_b, type1_b, value1_b_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpackBase__1 op1_b fpcr fpexc isbfloat16)
    let type1_b : FPType := tup__0
    let sign1_b : (BitVec 1) := tup__1
    let value1_b_name : real := tup__2
    (pure (sign1_b, type1_b, value1_b_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2_a, type2_a, value2_a_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpackBase__1 op2_a fpcr fpexc isbfloat16)
    let type2_a : FPType := tup__0
    let sign2_a : (BitVec 1) := tup__1
    let value2_a_name : real := tup__2
    (pure (sign2_a, type2_a, value2_a_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2_b, type2_b, value2_b_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpackBase__1 op2_b fpcr fpexc isbfloat16)
    let type2_b : FPType := tup__0
    let sign2_b : (BitVec 1) := tup__1
    let value2_b_name : real := tup__2
    (pure (sign2_b, type2_b, value2_b_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let inf1_a : Bool := (BEq.beq type1_a FPType_Infinity)
  let zero1_a : Bool := (BEq.beq type1_a FPType_Zero)
  let inf1_b : Bool := (BEq.beq type1_b FPType_Infinity)
  let zero1_b : Bool := (BEq.beq type1_b FPType_Zero)
  let inf2_a : Bool := (BEq.beq type2_a FPType_Infinity)
  let zero2_a : Bool := (BEq.beq type2_a FPType_Zero)
  let inf2_b : Bool := (BEq.beq type2_b FPType_Infinity)
  let zero2_b : Bool := (BEq.beq type2_b FPType_Zero)
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs4 type1_a type1_b type2_a type2_b op1_a op1_b op2_a op2_b fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  let result ← (( do
    if ((((inf1_a && zero2_a) || (zero1_a && inf2_a)) && ((inf1_b && zero2_b) || (zero1_b && inf2_b))) : Bool)
    then
      (do
        let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
        if (fpexc : Bool)
        then (FPProcessException FPExc_InvalidOp fpcr)
        else (pure ())
        (pure result))
    else (pure result) ) : SailM (BitVec k_N) )
  if ((! done) : Bool)
  then
    (do
      let signPa : (BitVec 1) := (sign1_a ^^^ sign2_a)
      let signPb : (BitVec 1) := (sign1_b ^^^ sign2_b)
      let infPa : Bool := (inf1_a || inf2_a)
      let infPb : Bool := (inf1_b || inf2_b)
      let zeroPa : Bool := (zero1_a || zero2_a)
      let zeroPb : Bool := (zero1_b || zero2_b)
      let invalidop : Bool := (((((inf1_a && zero2_a) || (zero1_a && inf2_a)) || (inf1_b && zero2_b)) || (zero1_b && inf2_b)) || ((infPa && infPb) && (signPa != signPb)))
      if (invalidop : Bool)
      then
        (do
          let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
          if (fpexc : Bool)
          then (FPProcessException FPExc_InvalidOp fpcr)
          else (pure ())
          (pure result))
      else
        (do
          if (((infPa && (signPa == 0#1)) || (infPb && (signPb == 0#1))) : Bool)
          then (do (FPInfinity 0#1 (Sail.BitVec.length result)))
          else
            (do
              if (((infPa && (signPa == 1#1)) || (infPb && (signPb == 1#1))) : Bool)
              then (do (FPInfinity 1#1 (Sail.BitVec.length result)))
              else
                (do
                  if (((zeroPa && zeroPb) && (signPa == signPb)) : Bool)
                  then (do (FPZero signPa (Sail.BitVec.length result)))
                  else
                    (do
                      let result_value : real := (add_real (mult_real value1_a_name value2_a_name) (mult_real value1_b_name value2_b_name))
                      if ((eq_real result_value (0)) : Bool)
                      then
                        (do
                          let result_sign : (BitVec 1) :=
                            if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                            then 1#1
                            else 0#1
                          (FPZero result_sign (Sail.BitVec.length result)))
                      else (do (FPRound__2 result_value fpcr rounding fpexc (Sail.BitVec.length result))))))))
  else (pure result)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFNeg (op : (BitVec k_N)) : SailM (BitVec k_N) := do
  sail_assert ((Sail.BitVec.length op) == 16) "src/v8_base.sail:32442.19-32442.20"
  let honor_altfp : Bool := true
  (BFNeg__1 op honor_altfp)

/-- Type quantifiers: k_cold_reset : Bool -/
def AArch64_ResetControlRegisters (cold_reset : Bool) : SailM Unit := do
  writeReg PSTATE { (← readReg PSTATE) with ZA := 0#1 }
  writeReg PSTATE { (← readReg PSTATE) with SM := 0#1 }
  writeReg PSTATE { (← readReg PSTATE) with ALLINT := 0#1 }
  writeReg PSTATE { (← readReg PSTATE) with EXLOCK := 0#1 }
  (ResetControlRegisters cold_reset)
  (pure (_TLBInvalidate ()))

def AArch64_CheckFPAdvSIMDEnabled (_ : Unit) : SailM Unit := do
  (AArch64_CheckFPEnabled ())
  if ((←((HaveSME ()) <&&> (do
       (pure ((← readReg PSTATE).SM == 1#1))) <&&> (do
       (pure (! (← (IsFullA64Enabled ()))))))) : Bool)
  then (SMEAccessTrap SMEExceptionType_Streaming (← readReg PSTATE).EL)
  else (pure ())

def CheckFPEnabled64 (_ : Unit) : SailM Unit := do
  (AArch64_CheckFPEnabled ())

def SPEToCollectSample (_ : Unit) : SailM Bool := SailME.run do
  if ((IsZero (_get_PMSICR_EL1_Type_COUNT (← readReg PMSICR_EL1))) : Bool)
  then (SPEResetSampleCounter ())
  else
    (do
      writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSICR_EL1) 31 0 (BitVec.subInt (_get_PMSICR_EL1_Type_COUNT (← readReg PMSICR_EL1)) 1))
      if ((IsZero (_get_PMSICR_EL1_Type_COUNT (← readReg PMSICR_EL1))) : Bool)
      then
        (do
          if ((←((pure ((_get_PMSIRR_EL1_Type_RND (← readReg PMSIRR_EL1)) == 1#1)) <&&> (do
               (pure ((_get_PMSIDR_EL1_Type_ERnd (← readReg PMSIDR_EL1)) == 1#1))))) : Bool)
          then writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSICR_EL1) 63 56 (← (SPEGetRandomInterval ())))
          else SailME.throw (true : Bool))
      else (pure ()))
  if (((BitVec.toNat (_get_PMSICR_EL1_Type_ECOUNT (← readReg PMSICR_EL1))) != 0) : Bool)
  then
    (do
      writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSICR_EL1) 63 56 (BitVec.subInt (_get_PMSICR_EL1_Type_ECOUNT (← readReg PMSICR_EL1)) 1))
      if ((IsZero (_get_PMSICR_EL1_Type_ECOUNT (← readReg PMSICR_EL1))) : Bool)
      then SailME.throw (true : Bool)
      else (pure ()))
  else (pure ())
  (pure false)

def SPESampleMemCopy (_ : Unit) : SailM Unit := do
  let loads_pass_filter ← (( do (pure ((_get_PMSFCR_EL1_Type_FT (← readReg PMSFCR_EL1)) == 1#1)) <&&> (do (pure ((_get_PMSFCR_EL1_Type_LD (← readReg PMSFCR_EL1)) == 1#1))) ) : SailM Bool )
  let stores_pass_filter ← (( do (pure ((_get_PMSFCR_EL1_Type_FT (← readReg PMSFCR_EL1)) == 1#1)) <&&> (do (pure ((_get_PMSFCR_EL1_Type_ST (← readReg PMSFCR_EL1)) == 1#1))) ) : SailM Bool )
  let record_load ← (( do (undefined_bool ()) ) : SailM Bool )
  let record_load ← (( do
    if ((loads_pass_filter && (! stores_pass_filter)) : Bool)
    then (pure true)
    else
      (do
        if (((! loads_pass_filter) && stores_pass_filter) : Bool)
        then (pure false)
        else (do (SPEGetRandomBoolean ()))) ) : SailM Bool )
  writeReg SPESampleClass 0b01#2
  let ldst : (BitVec 1) :=
    if (record_load : Bool)
    then 0#1
    else 1#1
  writeReg SPESampleSubclass (Sail.BitVec.updateSubrange (← readReg SPESampleSubclass) 7 0 (0b0010000#7 +++ ldst))
  writeReg SPESampleSubclassValid true
  writeReg SPESampleOpType (if (record_load : Bool)
  then OpType_Load
  else OpType_Store)

def DebugRestorePSR (_ : Unit) : SailM Unit := do
  if ((← (UsingAArch32 ())) : Bool)
  then
    (do
      let spsr ← (( do (SPSR_read (N := 32)) ) : SailM (BitVec 32) )
      (SetPSTATEFromPSR spsr)
      let split_vec ← do (__UNKNOWN_bits 13)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 12 12) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 11 11) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 10 10) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 9 9) }
      writeReg PSTATE { (← readReg PSTATE) with Q := (Sail.BitVec.extractLsb split_vec 8 8) }
      writeReg PSTATE { (← readReg PSTATE) with GE := (Sail.BitVec.extractLsb split_vec 7 4) }
      writeReg PSTATE { (← readReg PSTATE) with SS := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with A := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb split_vec 0 0) }
      writeReg PSTATE { (← readReg PSTATE) with IT := 0b00000000#8 }
      writeReg PSTATE { (← readReg PSTATE) with T := 1#1 }
      (DLR_write (← (__UNKNOWN_bits 32)))
      (DSPSR_write (Mk_DSPSR_Type (← (__UNKNOWN_bits 32)))))
  else
    (do
      let spsr ← (( do (SPSR_read (N := 64)) ) : SailM (BitVec 64) )
      (SetPSTATEFromPSR spsr)
      let split_vec ← do (__UNKNOWN_bits 9)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 8 8) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 7 7) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 6 6) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 5 5) }
      writeReg PSTATE { (← readReg PSTATE) with SS := (Sail.BitVec.extractLsb split_vec 4 4) }
      writeReg PSTATE { (← readReg PSTATE) with D := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with A := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb split_vec 0 0) }
      writeReg DLR_EL0 (← (__UNKNOWN_bits 64))
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type (← (__UNKNOWN_bits 64))))
  (UpdateEDSCRFields ())

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV86 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap6_IMPLEMENTED enabled
  if (enabled : Bool)
  then (__ConfigureV85 enabled)
  else (pure ())

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV90 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap0_IMPLEMENTED enabled
  if (enabled : Bool)
  then (__ConfigureV85 enabled)
  else (pure ())

/-- Type quantifiers: CRm : Int, CRn : Int, nreg : Int -/
def AArch32_CheckCP15InstrCoarseTraps (CRn : Int) (nreg : Int) (CRm : Int) : SailM Unit := do
  let major ← (( do (undefined_int ()) ) : SailM Int )
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <&&> (do
       (pure (! (← (ELUsingAArch32 EL1)))) <||> (do
         (EL2Enabled ()) <&&> (do
           (pure (! (← (ELUsingAArch32 EL2))))))))) : Bool)
  then (AArch64_CheckCP15InstrCoarseTraps CRn nreg CRm)
  else (pure ())
  let trapped_encoding : Bool := ((((CRn == 9) && ((CRm == 0) || ((CRm == 1) || ((CRm == 2) || ((CRm == 5) || ((CRm == 6) || ((CRm == 7) || (CRm == 8)))))))) || ((CRn == 10) && ((CRm == 0) || ((CRm == 1) || ((CRm == 4) || (CRm == 8)))))) || ((CRn == 11) && ((CRm == 0) || ((CRm == 1) || ((CRm == 2) || ((CRm == 3) || ((CRm == 4) || ((CRm == 5) || ((CRm == 6) || ((CRm == 7) || ((CRm == 8) || (CRm == 15))))))))))))
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
       (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
       (EL2Enabled ())))) : Bool)
  then
    (do
      let major :=
        if ((nreg == 1) : Bool)
        then CRn
        else CRm
      sail_assert ((0 ≤b major) && (major <b 32)) "src/v8_base.sail:41574.54-41574.55"
      if ((←((pure (! ((major == 4) || (major == 14)))) <&&> (do
           (pure ((BitVec.join1 [(BitVec.access (← (HSTR_read ())) major)]) == 1#1))) <||> (do
           (pure ((((_get_HCR_Type_TIDCP (← (HCR_read ()))) == 1#1) && (nreg == 1)) && trapped_encoding))))) : Bool)
      then
        (do
          if ((←((pure ((← readReg PSTATE).EL == EL0)) <&&> (do
               (__IMPDEF_boolean "UNDEF unallocated CP15 access at EL0")))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (pure ())
          if ((← (ELUsingAArch32 EL2)) : Bool)
          then (AArch32_SystemAccessTrap M32_Hyp (BitVec.toNat 0x3#4))
          else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x3#4)))
      else (pure ()))
  else (pure ())

def AArch32_ExceptionReturn (new_pc_in : (BitVec 32)) (spsr : (BitVec 32)) : SailM Unit := do
  let new_pc : (BitVec 32) := new_pc_in
  let _ : Unit := (SynchronizeContext ())
  writeReg __InstructionStep false
  (SetPSTATEFromPSR spsr)
  let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
  (SendEventLocal ())
  let new_pc ← (( do
    if (((← readReg PSTATE).IL == 1#1) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange new_pc 1 0 (← (__UNKNOWN_bits 2)))))
    else
      (do
        if (((← readReg PSTATE).T == 1#1) : Bool)
        then (pure (BitVec.update new_pc 0 (Bit 0#1)))
        else (pure (Sail.BitVec.updateSubrange new_pc 1 0 0b00#2))) ) : SailM (BitVec 32) )
  let branch_conditional ← (( do
    (pure (! (← (do
          let b__0 ← do (AArch32_CurrentCond ())
          if (((Sail.BitVec.extractLsb b__0 3 1) == (0b111#3 : (BitVec 3))) : Bool)
          then (pure true)
          else (pure false))))) ) : SailM Bool )
  (BranchTo new_pc BranchType_ERET branch_conditional)
  (CheckExceptionCatch false)

/-- Type quantifiers: k_cold_reset : Bool -/
def AArch32_ResetControlRegisters (cold_reset : Bool) : SailM Unit := do
  writeReg PSTATE { (← readReg PSTATE) with SS := 0#1 }
  (ResetControlRegisters cold_reset)
  (pure (_TLBInvalidate ()))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPRound (op : real) (fpcr : (BitVec 64)) (N : Nat) : SailM (BitVec N) := do
  (FPRound__1 op fpcr (← (FPRoundingMode fpcr)) N)

/-- Type quantifiers: k_M : Nat, N : Nat, fbits : Int, k_is_unsigned : Bool, List.elem N [16, 32, 64] ∧ List.elem k_M [16, 32, 64] -/
def FixedToFP (op : (BitVec k_M)) (fbits : Int) (is_unsigned : Bool) (fpcr : (BitVec 64)) (rounding : FPRounding) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:15912.38-15912.39"
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:15913.41-15913.42"
  let result ← (( do (undefined_bitvector N) ) : SailM (BitVec N) )
  sail_assert (fbits ≥b 0) "src/v8_base.sail:15915.21-15915.22"
  sail_assert (bne rounding FPRounding_ODD) "src/v8_base.sail:15916.37-15916.38"
  let int_operand ← do (asl_Int op is_unsigned)
  let real_operand : real := (div_real (to_real int_operand) (real_power (2) fbits))
  if ((eq_real real_operand (0)) : Bool)
  then (do (FPZero 0#1 N))
  else (do (FPRound__1 real_operand fpcr rounding N))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPAbs (op : (BitVec k_N)) : SailM (BitVec k_N) := SailME.run do
  let fptype ← (( do (undefined_FPType ()) ) : SailME (BitVec k_N) FPType )
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:16099.41-16099.42"
  if ((←((pure (! (← (UsingAArch32 ())))) <&&> (do
       (HaveAltFP ())))) : Bool)
  then
    (do
      let fpcr ← (( do (FPCR_read ()) ) : SailME (BitVec k_N) FPCRType )
      if (((_get_FPCRType_AH fpcr) == 1#1) : Bool)
      then
        (do
          let fptype ← (( do
            let (__tup_0, _, _) ← do (FPUnpack__1 op fpcr false)
            (pure __tup_0) ) : SailME (BitVec k_N) FPType )
          if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
          then SailME.throw (op : (BitVec k_N))
          else (pure ()))
      else (pure ()))
  else (pure ())
  (pure (0#1 +++ (Sail.BitVec.extractLsb op ((Sail.BitVec.length op) -i 2) 0)))

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPAdd__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let result_sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length result) == 64))) "src/v8_base.sail:16263.41-16263.42"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1 fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2 fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs__1 type1 type2 op1 op2 fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let result ← (( do
        if (((inf1 && inf2) && (sign1 == (Complement.complement sign2))) : Bool)
        then
          (do
            let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
            if (fpexc : Bool)
            then (FPProcessException FPExc_InvalidOp fpcr)
            else (pure ())
            (pure result))
        else
          (do
            if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 0#1))) : Bool)
            then (do (FPInfinity 0#1 (Sail.BitVec.length result)))
            else
              (do
                if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 1#1))) : Bool)
                then (do (FPInfinity 1#1 (Sail.BitVec.length result)))
                else
                  (do
                    if (((zero1 && zero2) && (sign1 == sign2)) : Bool)
                    then (do (FPZero sign1 (Sail.BitVec.length result)))
                    else
                      (do
                        let result_value : real := (add_real value1_name value2_name)
                        if ((eq_real result_value (0)) : Bool)
                        then
                          (do
                            let result_sign : (BitVec 1) :=
                              if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                              then 1#1
                              else 0#1
                            (FPZero result_sign (Sail.BitVec.length result)))
                        else (do (FPRound__2 result_value fpcr rounding fpexc (Sail.BitVec.length result))))))) ) : SailM (BitVec k_N) )
      if (fpexc : Bool)
      then (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
      else (pure ())
      (pure result))
  else (pure result)

/-- Type quantifiers: k_N : Nat, k_signal_nans : Bool, List.elem k_N [16, 32, 64] -/
def FPCompare (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (signal_nans : Bool) (fpcr : (BitVec 64)) : SailM (BitVec 4) := do
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:16326.41-16326.42"
  let (type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (type1, value1_name)) ) : SailM (FPType × real) )
  let (type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (type2, value2_name)) ) : SailM (FPType × real) )
  let result ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))) : Bool)
  then
    (do
      let result : (BitVec 4) := 0b0011#4
      if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) || signal_nans) : Bool)
      then (FPProcessException FPExc_InvalidOp fpcr)
      else (pure ())
      (pure result))
  else
    (do
      let result : (BitVec 4) :=
        if ((eq_real value1_name value2_name) : Bool)
        then 0b0110#4
        else
          (if ((lt_real value1_name value2_name) : Bool)
          then 0b1000#4
          else 0b0010#4)
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
      (pure result))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPCompareEQ (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM Bool := do
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:16359.41-16359.42"
  let (type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (type1, value1_name)) ) : SailM (FPType × real) )
  let (type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (type2, value2_name)) ) : SailM (FPType × real) )
  let result ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))) : Bool)
  then
    (do
      let result : Bool := false
      if (((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) : Bool)
      then (FPProcessException FPExc_InvalidOp fpcr)
      else (pure ())
      (pure result))
  else
    (do
      let result : Bool := (eq_real value1_name value2_name)
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
      (pure result))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPCompareGE (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM Bool := do
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:16386.41-16386.42"
  let (type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (type1, value1_name)) ) : SailM (FPType × real) )
  let (type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (type2, value2_name)) ) : SailM (FPType × real) )
  let result ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))) : Bool)
  then
    (do
      let result : Bool := false
      (FPProcessException FPExc_InvalidOp fpcr)
      (pure result))
  else
    (do
      let result : Bool := (gteq_real value1_name value2_name)
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
      (pure result))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPCompareGT (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM Bool := do
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:16410.41-16410.42"
  let (type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (type1, value1_name)) ) : SailM (FPType × real) )
  let (type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (type2, value2_name)) ) : SailM (FPType × real) )
  let result ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))) : Bool)
  then
    (do
      let result : Bool := false
      (FPProcessException FPExc_InvalidOp fpcr)
      (pure result))
  else
    (do
      let result : Bool := (gt_real value1_name value2_name)
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
      (pure result))

/-- Type quantifiers: M : Nat, k_N : Nat, List.elem M [16, 32, 64] ∧ List.elem k_N [16, 32, 64] -/
def FPConvert (op : (BitVec k_N)) (fpcr : (BitVec 64)) (rounding : FPRounding) (M : Nat) : SailM (BitVec M) := do
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert ((M == 16) || ((M == 32) || (M == 64))) "src/v8_base.sail:16508.38-16508.39"
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:16509.41-16509.42"
  let result ← (( do (undefined_bitvector M) ) : SailM (BitVec M) )
  let (fptype, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpackCV op fpcr)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  let alt_hp : Bool := ((M == 16) && ((_get_FPCRType_AHP fpcr) == 1#1))
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then
    (do
      let result ← (( do
        if (alt_hp : Bool)
        then (do (FPZero sign M))
        else
          (do
            if (((_get_FPCRType_DN fpcr) == 1#1) : Bool)
            then (do (FPDefaultNaN__1 fpcr M))
            else (do (FPConvertNaN op M))) ) : SailM (BitVec M) )
      if (((BEq.beq fptype FPType_SNaN) || alt_hp) : Bool)
      then (FPProcessException FPExc_InvalidOp fpcr)
      else (pure ())
      (pure result))
  else
    (do
      if ((BEq.beq fptype FPType_Infinity) : Bool)
      then
        (do
          if (alt_hp : Bool)
          then
            (do
              let result : (BitVec M) := (sign +++ (Ones (n := (M -i 1))))
              (FPProcessException FPExc_InvalidOp fpcr)
              (pure result))
          else (do (FPInfinity sign M)))
      else
        (do
          if ((BEq.beq fptype FPType_Zero) : Bool)
          then (do (FPZero sign M))
          else
            (do
              let result ← (FPRoundCV value_name fpcr rounding M)
              (FPProcessDenorm fptype (Sail.BitVec.length op) fpcr)
              (pure result))))

/-- Type quantifiers: k_N : Nat, k_altfp : Bool, List.elem k_N [16, 32, 64] -/
def FPMax__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) (altfp : Bool) : SailM (BitVec k_N) := do
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:16634.41-16634.42"
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let fpcr : FPCRType := fpcr_in
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  if ((((altfp && (BEq.beq type1 FPType_Zero)) && (BEq.beq type2 FPType_Zero)) && (sign1 != sign2)) : Bool)
  then (FPZero sign2 (Sail.BitVec.length result))
  else
    (do
      if ((altfp && (((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN)))) : Bool)
      then
        (do
          (FPProcessException FPExc_InvalidOp fpcr)
          if ((BEq.beq type2 FPType_Zero) : Bool)
          then (FPZero sign2 (Sail.BitVec.length result))
          else (pure op2))
      else
        (do
          let (done, result) ← (( do
            let (tup__0, tup__1) ← do (FPProcessNaNs type1 type2 op1 op2 fpcr)
            let done : Bool := tup__0
            let result : (BitVec k_N) := tup__1
            (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
          if ((! done) : Bool)
          then
            (do
              let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
              let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
              let value_name ← (( do (undefined_real ()) ) : SailM real )
              let (fptype, sign, value_name) : (FPType × (BitVec 1) × real) :=
                if ((gt_real value1_name value2_name) : Bool)
                then
                  (let (tup__0, tup__1, tup__2) := ((type1, sign1, value1_name) : (FPType × (BitVec 1) × real))
                  let fptype : FPType := tup__0
                  let sign : (BitVec 1) := tup__1
                  let value_name : real := tup__2
                  (fptype, sign, value_name))
                else
                  (let (tup__0, tup__1, tup__2) := ((type2, sign2, value2_name) : (FPType × (BitVec 1) × real))
                  let fptype : FPType := tup__0
                  let sign : (BitVec 1) := tup__1
                  let value_name : real := tup__2
                  (fptype, sign, value_name))
              let (fpcr, result) ← (( do
                if ((BEq.beq fptype FPType_Infinity) : Bool)
                then
                  (do
                    let result ← (FPInfinity sign (Sail.BitVec.length result))
                    (pure (fpcr, result)))
                else
                  (do
                    let (fpcr, result) ← (( do
                      if ((BEq.beq fptype FPType_Zero) : Bool)
                      then
                        (do
                          let sign : (BitVec 1) := (sign1 &&& sign2)
                          let result ← (FPZero sign (Sail.BitVec.length result))
                          (pure (fpcr, result)))
                      else
                        (do
                          let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
                          let fpcr : (BitVec 64) :=
                            if (altfp : Bool)
                            then
                              (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 24 24 0#1)
                              (Sail.BitVec.updateSubrange fpcr 19 19 0#1))
                            else fpcr
                          let result ← (FPRound__2 value_name fpcr rounding true (Sail.BitVec.length result))
                          (pure (fpcr, result))) ) : SailM ((BitVec 64) × (BitVec k_N)) )
                    (pure (fpcr, result))) ) : SailM ((BitVec 64) × (BitVec k_N)) )
              (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
              (pure result))
          else (pure result)))

/-- Type quantifiers: k_N : Nat, k_altfp : Bool, List.elem k_N [16, 32, 64] -/
def FPMin__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) (altfp : Bool) : SailM (BitVec k_N) := do
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:16735.41-16735.42"
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let fpcr : FPCRType := fpcr_in
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  if ((((altfp && (BEq.beq type1 FPType_Zero)) && (BEq.beq type2 FPType_Zero)) && (sign1 != sign2)) : Bool)
  then (FPZero sign2 (Sail.BitVec.length result))
  else
    (do
      if ((altfp && (((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN)))) : Bool)
      then
        (do
          (FPProcessException FPExc_InvalidOp fpcr)
          if ((BEq.beq type2 FPType_Zero) : Bool)
          then (FPZero sign2 (Sail.BitVec.length result))
          else (pure op2))
      else
        (do
          let (done, result) ← (( do
            let (tup__0, tup__1) ← do (FPProcessNaNs type1 type2 op1 op2 fpcr)
            let done : Bool := tup__0
            let result : (BitVec k_N) := tup__1
            (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
          if ((! done) : Bool)
          then
            (do
              let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
              let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
              let value_name ← (( do (undefined_real ()) ) : SailM real )
              let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
              let (fptype, sign, value_name) : (FPType × (BitVec 1) × real) :=
                if ((lt_real value1_name value2_name) : Bool)
                then
                  (let (tup__0, tup__1, tup__2) := ((type1, sign1, value1_name) : (FPType × (BitVec 1) × real))
                  let fptype : FPType := tup__0
                  let sign : (BitVec 1) := tup__1
                  let value_name : real := tup__2
                  (fptype, sign, value_name))
                else
                  (let (tup__0, tup__1, tup__2) := ((type2, sign2, value2_name) : (FPType × (BitVec 1) × real))
                  let fptype : FPType := tup__0
                  let sign : (BitVec 1) := tup__1
                  let value_name : real := tup__2
                  (fptype, sign, value_name))
              let (fpcr, result) ← (( do
                if ((BEq.beq fptype FPType_Infinity) : Bool)
                then
                  (do
                    let result ← (FPInfinity sign (Sail.BitVec.length result))
                    (pure (fpcr, result)))
                else
                  (do
                    let (fpcr, result) ← (( do
                      if ((BEq.beq fptype FPType_Zero) : Bool)
                      then
                        (do
                          let sign : (BitVec 1) := (sign1 ||| sign2)
                          let result ← (FPZero sign (Sail.BitVec.length result))
                          (pure (fpcr, result)))
                      else
                        (do
                          let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
                          let fpcr : (BitVec 64) :=
                            if (altfp : Bool)
                            then
                              (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 24 24 0#1)
                              (Sail.BitVec.updateSubrange fpcr 19 19 0#1))
                            else fpcr
                          let result ← (FPRound__2 value_name fpcr rounding true (Sail.BitVec.length result))
                          (pure (fpcr, result))) ) : SailM ((BitVec 64) × (BitVec k_N)) )
                    (pure (fpcr, result))) ) : SailM ((BitVec 64) × (BitVec k_N)) )
              (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
              (pure result))
          else (pure result)))

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPMulAdd__1 (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let infA ← (( do (undefined_bool ()) ) : SailM Bool )
  let infP ← (( do (undefined_bool ()) ) : SailM Bool )
  let invalidop ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let result_sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let signA ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let signP ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let typeA ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let valueA_name ← (( do (undefined_real ()) ) : SailM real )
  let zeroA ← (( do (undefined_bool ()) ) : SailM Bool )
  let zeroP ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length result) == 64))) "src/v8_base.sail:16945.41-16945.42"
  let (signA, typeA, valueA_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 addend fpcr fpexc)
    let typeA : FPType := tup__0
    let signA : (BitVec 1) := tup__1
    let valueA_name : real := tup__2
    (pure (signA, typeA, valueA_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1 fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2 fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
  let zero1 : Bool := (BEq.beq type1 FPType_Zero)
  let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
  let zero2 : Bool := (BEq.beq type2 FPType_Zero)
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs3__1 typeA type1 type2 addend op1 op2 fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  let result ← (( do
    if ((! ((←((HaveAltFP ()) <&&> (do
             (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) : Bool)
    then
      (do
        if (((BEq.beq typeA FPType_QNaN) && ((inf1 && zero2) || (zero1 && inf2))) : Bool)
        then
          (do
            let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
            if (fpexc : Bool)
            then (FPProcessException FPExc_InvalidOp fpcr)
            else (pure ())
            (pure result))
        else (pure result))
    else (pure result) ) : SailM (BitVec k_N) )
  if ((! done) : Bool)
  then
    (do
      let infA : Bool := (BEq.beq typeA FPType_Infinity)
      let zeroA : Bool := (BEq.beq typeA FPType_Zero)
      let signP : (BitVec 1) := (sign1 ^^^ sign2)
      let infP : Bool := (inf1 || inf2)
      let zeroP : Bool := (zero1 || zero2)
      let invalidop : Bool := (((inf1 && zero2) || (zero1 && inf2)) || ((infA && infP) && (signA != signP)))
      let result ← (( do
        if (invalidop : Bool)
        then
          (do
            let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
            if (fpexc : Bool)
            then (FPProcessException FPExc_InvalidOp fpcr)
            else (pure ())
            (pure result))
        else
          (do
            if (((infA && (signA == 0#1)) || (infP && (signP == 0#1))) : Bool)
            then (do (FPInfinity 0#1 (Sail.BitVec.length result)))
            else
              (do
                if (((infA && (signA == 1#1)) || (infP && (signP == 1#1))) : Bool)
                then (do (FPInfinity 1#1 (Sail.BitVec.length result)))
                else
                  (do
                    if (((zeroA && zeroP) && (signA == signP)) : Bool)
                    then (do (FPZero signA (Sail.BitVec.length result)))
                    else
                      (do
                        let result_value : real := (add_real valueA_name (mult_real value1_name value2_name))
                        if ((eq_real result_value (0)) : Bool)
                        then
                          (do
                            let result_sign : (BitVec 1) :=
                              if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                              then 1#1
                              else 0#1
                            (FPZero result_sign (Sail.BitVec.length result)))
                        else (do (FPRound__2 result_value fpcr rounding fpexc (Sail.BitVec.length result))))))) ) : SailM (BitVec k_N) )
      if (((! invalidop) && fpexc) : Bool)
      then (FPProcessDenorms3 typeA type1 type2 (Sail.BitVec.length result) fpcr)
      else (pure ())
      (pure result))
  else (pure result)

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 32 -/
def FPMulAddH__1 (addend : (BitVec k_N)) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let infA ← (( do (undefined_bool ()) ) : SailM Bool )
  let infP ← (( do (undefined_bool ()) ) : SailM Bool )
  let invalidop ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length addend)) ) : SailM (BitVec k_N) )
  let result_sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let signA ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let signP ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let typeA ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let valueA_name ← (( do (undefined_real ()) ) : SailM real )
  let zeroA ← (( do (undefined_bool ()) ) : SailM Bool )
  let zeroP ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert ((Sail.BitVec.length result) == 32) "src/v8_base.sail:17149.19-17149.20"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let (signA, typeA, valueA_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 addend fpcr fpexc)
    let typeA : FPType := tup__0
    let signA : (BitVec 1) := tup__1
    let valueA_name : real := tup__2
    (pure (signA, typeA, valueA_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1 fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2 fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
  let zero1 : Bool := (BEq.beq type1 FPType_Zero)
  let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
  let zero2 : Bool := (BEq.beq type2 FPType_Zero)
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs3H typeA type1 type2 addend op1 op2 fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  let result ← (( do
    if ((! ((←((HaveAltFP ()) <&&> (do
             (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) : Bool)
    then
      (do
        if (((BEq.beq typeA FPType_QNaN) && ((inf1 && zero2) || (zero1 && inf2))) : Bool)
        then
          (do
            let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
            if (fpexc : Bool)
            then (FPProcessException FPExc_InvalidOp fpcr)
            else (pure ())
            (pure result))
        else (pure result))
    else (pure result) ) : SailM (BitVec k_N) )
  if ((! done) : Bool)
  then
    (do
      let infA : Bool := (BEq.beq typeA FPType_Infinity)
      let zeroA : Bool := (BEq.beq typeA FPType_Zero)
      let signP : (BitVec 1) := (sign1 ^^^ sign2)
      let infP : Bool := (inf1 || inf2)
      let zeroP : Bool := (zero1 || zero2)
      let invalidop : Bool := (((inf1 && zero2) || (zero1 && inf2)) || ((infA && infP) && (signA != signP)))
      let result ← (( do
        if (invalidop : Bool)
        then
          (do
            let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
            if (fpexc : Bool)
            then (FPProcessException FPExc_InvalidOp fpcr)
            else (pure ())
            (pure result))
        else
          (do
            if (((infA && (signA == 0#1)) || (infP && (signP == 0#1))) : Bool)
            then (do (FPInfinity 0#1 (Sail.BitVec.length result)))
            else
              (do
                if (((infA && (signA == 1#1)) || (infP && (signP == 1#1))) : Bool)
                then (do (FPInfinity 1#1 (Sail.BitVec.length result)))
                else
                  (do
                    if (((zeroA && zeroP) && (signA == signP)) : Bool)
                    then (do (FPZero signA (Sail.BitVec.length result)))
                    else
                      (do
                        let result_value : real := (add_real valueA_name (mult_real value1_name value2_name))
                        if ((eq_real result_value (0)) : Bool)
                        then
                          (do
                            let result_sign : (BitVec 1) :=
                              if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                              then 1#1
                              else 0#1
                            (FPZero result_sign (Sail.BitVec.length result)))
                        else (do (FPRound__2 result_value fpcr rounding fpexc (Sail.BitVec.length result))))))) ) : SailM (BitVec k_N) )
      if (((! invalidop) && fpexc) : Bool)
      then (FPProcessDenorm typeA (Sail.BitVec.length result) fpcr)
      else (pure ())
      (pure result))
  else (pure result)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPNeg (op : (BitVec k_N)) : SailM (BitVec k_N) := SailME.run do
  let fptype ← (( do (undefined_FPType ()) ) : SailME (BitVec k_N) FPType )
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:17222.41-17222.42"
  if ((←((pure (! (← (UsingAArch32 ())))) <&&> (do
       (HaveAltFP ())))) : Bool)
  then
    (do
      let fpcr ← (( do (FPCR_read ()) ) : SailME (BitVec k_N) FPCRType )
      if (((_get_FPCRType_AH fpcr) == 1#1) : Bool)
      then
        (do
          let fptype ← (( do
            let (__tup_0, _, _) ← do (FPUnpack__1 op fpcr false)
            (pure __tup_0) ) : SailME (BitVec k_N) FPType )
          if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
          then SailME.throw (op : (BitVec k_N))
          else (pure ()))
      else (pure ()))
  else (pure ())
  (pure ((Complement.complement (BitVec.join1 [(BitVec.access op ((Sail.BitVec.length op) -i 1))])) +++ (Sail.BitVec.extractLsb op ((Sail.BitVec.length op) -i 2) 0)))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPRecipEstimate (operand : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let estimate ← (( do (undefined_int ()) ) : SailM Int )
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length operand) == 16) || (((Sail.BitVec.length operand) == 32) || ((Sail.BitVec.length operand) == 64))) "src/v8_base.sail:17267.41-17267.42"
  let fpcr : FPCRType := fpcr_in
  let result ← (( do (undefined_bitvector (Sail.BitVec.length operand)) ) : SailM (BitVec k_N) )
  let overflow_to_inf ← (( do (undefined_bool ()) ) : SailM Bool )
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then (Sail.BitVec.updateSubrange fpcr 23 22 0b00#2)
    else fpcr
  let (fptype, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 operand fpcr fpexc)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then (do (FPProcessNaN__1 fptype operand fpcr fpexc))
  else
    (do
      if ((BEq.beq fptype FPType_Infinity) : Bool)
      then (do (FPZero sign (Sail.BitVec.length result)))
      else
        (do
          if ((BEq.beq fptype FPType_Zero) : Bool)
          then
            (do
              let result ← (FPInfinity sign (Sail.BitVec.length result))
              if (fpexc : Bool)
              then (FPProcessException FPExc_DivideByZero fpcr)
              else (pure ())
              (pure result))
          else
            (do
              if ((((((Sail.BitVec.length result) == 16) && (lt_real (abs_real value_name) (real_power (2) (Neg.neg 16)))) || (((Sail.BitVec.length result) == 32) && (lt_real (abs_real value_name) (real_power (2) (Neg.neg 128))))) || (((Sail.BitVec.length result) == 64) && (lt_real (abs_real value_name) (real_power (2) (Neg.neg 1024))))) : Bool)
              then
                (do
                  let overflow_to_inf : Bool :=
                    match rounding with
                    | .FPRounding_TIEEVEN => true
                    | .FPRounding_POSINF => (sign == 0#1)
                    | .FPRounding_NEGINF => (sign == 1#1)
                    | .FPRounding_ZERO => false
                    | _ => overflow_to_inf
                  let result ←
                    if (overflow_to_inf : Bool)
                    then (FPInfinity sign (Sail.BitVec.length result))
                    else (FPMaxNormal sign (Sail.BitVec.length result))
                  if (fpexc : Bool)
                  then
                    (do
                      (FPProcessException FPExc_Overflow fpcr)
                      (FPProcessException FPExc_Inexact fpcr))
                  else (pure ())
                  (pure result))
              else
                (do
                  if ((((((_get_FPCRType_FZ fpcr) == 1#1) && ((Sail.BitVec.length result) != 16)) || (((_get_FPCRType_FZ16 fpcr) == 1#1) && ((Sail.BitVec.length result) == 16))) && (((((Sail.BitVec.length result) == 16) && (gteq_real (abs_real value_name) (real_power (2) 14))) || (((Sail.BitVec.length result) == 32) && (gteq_real (abs_real value_name) (real_power (2) 126)))) || (((Sail.BitVec.length result) == 64) && (gteq_real (abs_real value_name) (real_power (2) 1022))))) : Bool)
                  then
                    (do
                      let result ← (FPZero sign (Sail.BitVec.length result))
                      if ((← (UsingAArch32 ())) : Bool)
                      then (FPSCR_write (_update_FPSCR_Type_UFC (← (FPSCR_read__1 ())) 1#1))
                      else
                        (do
                          if (fpexc : Bool)
                          then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 3 3 1#1)
                          else (pure ()))
                      (pure result))
                  else
                    (do
                      let fraction ← (( do (undefined_bitvector 52) ) : SailM (BitVec 52) )
                      let exp ← (( do (undefined_int ()) ) : SailM Int )
                      let (exp, fraction) : (Int × (BitVec 52)) :=
                        match (Sail.BitVec.length result) with
                        | 16 =>
                          (let fraction : (BitVec 52) := ((Sail.BitVec.extractLsb operand 9 0) +++ (Zeros (n := 42)))
                          let exp : Int := (BitVec.toNat (Sail.BitVec.extractLsb operand 14 10))
                          (exp, fraction))
                        | 32 =>
                          (let fraction : (BitVec 52) := ((Sail.BitVec.extractLsb operand 22 0) +++ (Zeros (n := 29)))
                          let exp : Int := (BitVec.toNat (Sail.BitVec.extractLsb operand 30 23))
                          (exp, fraction))
                        | 64 =>
                          (let fraction : (BitVec 52) := (Sail.BitVec.extractLsb operand 51 0)
                          let exp : Int := (BitVec.toNat (Sail.BitVec.extractLsb operand 62 52))
                          (exp, fraction))
                        | _ => (exp, fraction)
                      let (exp, fraction) : (Int × (BitVec 52)) :=
                        if ((exp == 0) : Bool)
                        then
                          (let (exp, fraction) : (Int × (BitVec 52)) :=
                            if (((BitVec.join1 [(BitVec.access fraction 51)]) == 0#1) : Bool)
                            then
                              (let exp : Int := (Neg.neg 1)
                              let fraction : (BitVec 52) := ((Sail.BitVec.extractLsb fraction 49 0) +++ 0b00#2)
                              (exp, fraction))
                            else
                              (let fraction : (BitVec 52) := ((Sail.BitVec.extractLsb fraction 50 0) +++ 0#1)
                              (exp, fraction))
                          (exp, fraction))
                        else (exp, fraction)
                      let exp := exp
                      let scaled ← (( do (undefined_range 0 4095) ) : SailM Nat )
                      let increasedprecision_name ← (( do (pure ((←((pure ((Sail.BitVec.length result) == 32)) <&&> (do (HaveFeatRPRES ())))) && altfp)) ) : SailM Bool )
                      let scaled : Nat :=
                        if ((! increasedprecision_name) : Bool)
                        then (BitVec.toNat (1#1 +++ (Sail.BitVec.extractLsb fraction 51 44)))
                        else (BitVec.toNat (1#1 +++ (Sail.BitVec.extractLsb fraction 51 41)))
                      let scaled := scaled
                      let result_exp ← (( do (undefined_int ()) ) : SailM Int )
                      let result_exp : Int :=
                        match (Sail.BitVec.length result) with
                        | 16 => (29 -i exp)
                        | 32 => (253 -i exp)
                        | 64 => (2045 -i exp)
                        | _ => result_exp
                      let estimate ← do (RecipEstimate scaled increasedprecision_name)
                      let fraction : (BitVec 52) :=
                        if ((! increasedprecision_name) : Bool)
                        then ((integer_subrange estimate 7 0) +++ (Zeros (n := 44)))
                        else ((integer_subrange estimate 11 0) +++ (Zeros (n := 40)))
                      let (fraction, result_exp) : ((BitVec 52) × Int) :=
                        if ((result_exp == 0) : Bool)
                        then
                          (let fraction : (BitVec 52) := (1#1 +++ (Sail.BitVec.extractLsb fraction 51 1))
                          (fraction, result_exp))
                        else
                          (let (fraction, result_exp) : ((BitVec 52) × Int) :=
                            if ((result_exp == (Neg.neg 1)) : Bool)
                            then
                              (let fraction : (BitVec 52) := (0b01#2 +++ (Sail.BitVec.extractLsb fraction 51 2))
                              let result_exp : Int := 0
                              (fraction, result_exp))
                            else (fraction, result_exp)
                          (fraction, result_exp))
                      let result_exp := result_exp
                      match (Sail.BitVec.length result) with
                      | 16 => (pure ((sign +++ (integer_subrange result_exp ((Sail.BitVec.length result) -i 12) 0)) +++ (Sail.BitVec.extractLsb fraction 51 42)))
                      | 32 => (pure ((sign +++ (integer_subrange result_exp ((Sail.BitVec.length result) -i 25) 0)) +++ (Sail.BitVec.extractLsb fraction 51 29)))
                      | 64 => (pure ((sign +++ (integer_subrange result_exp ((Sail.BitVec.length result) -i 54) 0)) +++ (Sail.BitVec.extractLsb fraction 51 0)))
                      | _ => (pure result))))))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPRecpX (op : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:17407.41-17407.42"
  let fpcr : FPCRType := fpcr_in
  let esize : Nat := 5
  let esize : Int :=
    match (Sail.BitVec.length op) with
    | 16 => 5
    | 32 => 8
    | 64 => 11
    | _ => esize
  let esize := esize
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op)) ) : SailM (BitVec k_N) )
  let exp ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let frac : (BitVec (k_N - (esize + 1))) := (Zeros (n := ((Sail.BitVec.length result) -i (esize +i 1))))
  let altfp ← (( do (pure ((← (HaveAltFP ())) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let (fptype, sign) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op fpcr fpexc)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, sign)) ) : SailM (FPType × (BitVec 1)) )
  let exp ← (( do
    match (Sail.BitVec.length result) with
    | 16 =>
      (do
        sail_assert ((10 ≤b ((10 +i esize) -i 1)) && (((10 +i esize) -i 1) <b (Sail.BitVec.length result))) "src/v8_base.sail:17434.75-17434.76"
        (pure (Sail.BitVec.extractLsb op ((10 +i esize) -i 1) 10)))
    | 32 =>
      (do
        sail_assert ((23 ≤b ((23 +i esize) -i 1)) && (((23 +i esize) -i 1) <b (Sail.BitVec.length result))) "src/v8_base.sail:17438.75-17438.76"
        (pure (Sail.BitVec.extractLsb op ((23 +i esize) -i 1) 23)))
    | 64 => (pure (Sail.BitVec.extractLsb op ((52 +i esize) -i 1) 52))
    | _ => (pure exp) ) : SailM (BitVec esize) )
  let max_exp : (BitVec esize) := (BitVec.subInt (Ones (n := esize)) 1)
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then (do (FPProcessNaN__1 fptype op fpcr fpexc))
  else
    (if ((IsZero exp) : Bool)
    then (pure ((sign +++ max_exp) +++ frac))
    else (pure ((sign +++ (Complement.complement exp)) +++ frac)))

/-- Type quantifiers: k_N : Nat, k_exact : Bool, List.elem k_N [16, 32, 64] -/
def FPRoundInt (op : (BitVec k_N)) (fpcr : (BitVec 64)) (rounding : FPRounding) (exact : Bool) : SailM (BitVec k_N) := do
  let error ← (( do (undefined_real ()) ) : SailM real )
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let int_result ← (( do (undefined_int ()) ) : SailM Int )
  let real_result ← (( do (undefined_real ()) ) : SailM real )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (bne rounding FPRounding_ODD) "src/v8_base.sail:17470.37-17470.38"
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:17471.41-17471.42"
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let (fptype, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op fpcr fpexc)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op)) ) : SailM (BitVec k_N) )
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then (do (FPProcessNaN fptype op fpcr))
  else
    (do
      if ((BEq.beq fptype FPType_Infinity) : Bool)
      then (do (FPInfinity sign (Sail.BitVec.length result)))
      else
        (do
          if ((BEq.beq fptype FPType_Zero) : Bool)
          then (do (FPZero sign (Sail.BitVec.length result)))
          else
            (do
              let int_result : Int := (round_down value_name)
              let error : real := (sub_real value_name (to_real int_result))
              let round_up ← (( do (undefined_bool ()) ) : SailM Bool )
              let round_up : Bool :=
                match rounding with
                | .FPRounding_TIEEVEN => ((gt_real error (1/2)) || ((eq_real error (1/2)) && ((BitVec.join1 [(integer_access int_result 0)]) == 1#1)))
                | .FPRounding_POSINF => (bne error (0))
                | .FPRounding_NEGINF => false
                | .FPRounding_ZERO => ((bne error (0)) && (int_result <b 0))
                | .FPRounding_TIEAWAY => ((gt_real error (1/2)) || ((eq_real error (1/2)) && (int_result ≥b 0)))
                | _ => round_up
              let int_result : Int :=
                if (round_up : Bool)
                then (int_result +i 1)
                else int_result
              let int_result := int_result
              let real_result : real := (to_real int_result)
              let result ← (( do
                if ((eq_real real_result (0)) : Bool)
                then (do (FPZero sign (Sail.BitVec.length result)))
                else (do (FPRound__1 real_result fpcr FPRounding_ZERO (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
              if (((bne error (0)) && exact) : Bool)
              then (FPProcessException FPExc_Inexact fpcr)
              else (pure ())
              (pure result))))

/-- Type quantifiers: k_N : Nat, intsize : Int, List.elem k_N [32, 64] -/
def FPRoundIntN (op : (BitVec k_N)) (fpcr : (BitVec 64)) (rounding : FPRounding) (intsize : Int) : SailM (BitVec k_N) := do
  let error ← (( do (undefined_real ()) ) : SailM real )
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let int_result ← (( do (undefined_int ()) ) : SailM Int )
  let overflow ← (( do (undefined_bool ()) ) : SailM Bool )
  let real_result ← (( do (undefined_real ()) ) : SailM real )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (bne rounding FPRounding_ODD) "src/v8_base.sail:17533.37-17533.38"
  sail_assert (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64)) "src/v8_base.sail:17534.30-17534.31"
  sail_assert ((intsize == 32) || (intsize == 64)) "src/v8_base.sail:17535.40-17535.41"
  let exp ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op)) ) : SailM (BitVec k_N) )
  let round_up ← (( do (undefined_bool ()) ) : SailM Bool )
  let E :=
    if (((Sail.BitVec.length result) == 32) : Bool)
    then 8
    else 11
  let F := ((Sail.BitVec.length result) -i (E +i 1))
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let (fptype, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op fpcr fpexc)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  if (((BEq.beq fptype FPType_SNaN) || ((BEq.beq fptype FPType_QNaN) || (BEq.beq fptype FPType_Infinity))) : Bool)
  then
    (do
      let result : (BitVec k_N) :=
        if (((Sail.BitVec.length result) == 32) : Bool)
        then
          (let exp := (126 +i intsize)
          ((1#1 +++ (integer_subrange exp (E -i 1) 0)) +++ (Zeros (n := F))))
        else
          (let exp := (1022 +i intsize)
          ((1#1 +++ (integer_subrange exp (E -i 1) 0)) +++ (Zeros (n := F))))
      (FPProcessException FPExc_InvalidOp fpcr)
      (pure result))
  else
    (do
      if ((BEq.beq fptype FPType_Zero) : Bool)
      then (do (FPZero sign (Sail.BitVec.length result)))
      else
        (do
          let int_result : Int := (round_down value_name)
          let error : real := (sub_real value_name (to_real int_result))
          let round_up : Bool :=
            match rounding with
            | .FPRounding_TIEEVEN => ((gt_real error (1/2)) || ((eq_real error (1/2)) && ((BitVec.join1 [(integer_access int_result 0)]) == 1#1)))
            | .FPRounding_POSINF => (bne error (0))
            | .FPRounding_NEGINF => false
            | .FPRounding_ZERO => ((bne error (0)) && (int_result <b 0))
            | .FPRounding_TIEAWAY => ((gt_real error (1/2)) || ((eq_real error (1/2)) && (int_result ≥b 0)))
            | _ => round_up
          let int_result : Int :=
            if (round_up : Bool)
            then (int_result +i 1)
            else int_result
          let int_result := int_result
          let overflow : Bool := ((int_result >b ((2 ^i (intsize -i 1)) -i 1)) || (int_result <b ((Neg.neg 1) *i (2 ^i (intsize -i 1)))))
          let (error, result) ← (( do
            if (overflow : Bool)
            then
              (do
                let result : (BitVec k_N) :=
                  if (((Sail.BitVec.length result) == 32) : Bool)
                  then
                    (let exp := (126 +i intsize)
                    ((1#1 +++ (integer_subrange exp (E -i 1) 0)) +++ (Zeros (n := F))))
                  else
                    (let exp := (1022 +i intsize)
                    ((1#1 +++ (integer_subrange exp (E -i 1) 0)) +++ (Zeros (n := F))))
                (FPProcessException FPExc_InvalidOp fpcr)
                let error : real := (0)
                (pure (error, result)))
            else
              (do
                let real_result : real := (to_real int_result)
                let result ← (( do
                  if ((eq_real real_result (0)) : Bool)
                  then (do (FPZero sign (Sail.BitVec.length result)))
                  else (do (FPRound__1 real_result fpcr FPRounding_ZERO (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                (pure (error, result))) ) : SailM (real × (BitVec k_N)) )
          if ((bne error (0)) : Bool)
          then (FPProcessException FPExc_Inexact fpcr)
          else (pure ())
          (pure result)))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPRSqrtEstimate (operand : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let estimate ← (( do (undefined_int ()) ) : SailM Int )
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length operand) == 16) || (((Sail.BitVec.length operand) == 32) || ((Sail.BitVec.length operand) == 64))) "src/v8_base.sail:17615.41-17615.42"
  let fpcr : FPCRType := fpcr_in
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let (fptype, sign) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 operand fpcr fpexc)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, sign)) ) : SailM (FPType × (BitVec 1)) )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length operand)) ) : SailM (BitVec k_N) )
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then (do (FPProcessNaN__1 fptype operand fpcr fpexc))
  else
    (do
      if ((BEq.beq fptype FPType_Zero) : Bool)
      then
        (do
          let result ← (FPInfinity sign (Sail.BitVec.length result))
          if (fpexc : Bool)
          then (FPProcessException FPExc_DivideByZero fpcr)
          else (pure ())
          (pure result))
      else
        (do
          if ((sign == 1#1) : Bool)
          then
            (do
              let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
              if (fpexc : Bool)
              then (FPProcessException FPExc_InvalidOp fpcr)
              else (pure ())
              (pure result))
          else
            (do
              if ((BEq.beq fptype FPType_Infinity) : Bool)
              then (do (FPZero 0#1 (Sail.BitVec.length result)))
              else
                (do
                  let fraction ← (( do (undefined_bitvector 52) ) : SailM (BitVec 52) )
                  let exp ← (( do (undefined_int ()) ) : SailM Int )
                  let (exp, fraction) : (Int × (BitVec 52)) :=
                    match (Sail.BitVec.length result) with
                    | 16 =>
                      (let fraction : (BitVec 52) := ((Sail.BitVec.extractLsb operand 9 0) +++ (Zeros (n := 42)))
                      let exp : Int := (BitVec.toNat (Sail.BitVec.extractLsb operand 14 10))
                      (exp, fraction))
                    | 32 =>
                      (let fraction : (BitVec 52) := ((Sail.BitVec.extractLsb operand 22 0) +++ (Zeros (n := 29)))
                      let exp : Int := (BitVec.toNat (Sail.BitVec.extractLsb operand 30 23))
                      (exp, fraction))
                    | 64 =>
                      (let fraction : (BitVec 52) := (Sail.BitVec.extractLsb operand 51 0)
                      let exp : Int := (BitVec.toNat (Sail.BitVec.extractLsb operand 62 52))
                      (exp, fraction))
                    | _ => (exp, fraction)
                  let (exp, fraction) ← (( do
                    if ((exp == 0) : Bool)
                    then
                      (do
                        let (exp, fraction) ← (( do
                          let mut loop_vars := (exp, fraction)
                          while (λ (exp, fraction) => ((BitVec.join1 [(BitVec.access fraction 51)]) == 0#1)) loop_vars do
                            let (exp, fraction) := loop_vars
                            loop_vars :=
                              (let fraction : (BitVec 52) := ((Sail.BitVec.extractLsb fraction 50 0) +++ 0#1)
                              let exp : Int := (exp -i 1)
                              (exp, fraction) : (Int × (BitVec 52)))
                          (pure loop_vars) ) : SailM (Int × (BitVec 52)) )
                        let fraction : (BitVec 52) := ((Sail.BitVec.extractLsb fraction 50 0) +++ 0#1)
                        (pure (exp, fraction)))
                    else (pure (exp, fraction)) ) : SailM (Int × (BitVec 52)) )
                  let fraction := fraction
                  let exp := exp
                  let scaled ← (( do (undefined_range 0 4095) ) : SailM Nat )
                  let increasedprecision_name ← (( do (pure ((←((pure ((Sail.BitVec.length result) == 32)) <&&> (do (HaveFeatRPRES ())))) && altfp)) ) : SailM Bool )
                  let scaled : Nat :=
                    if ((! increasedprecision_name) : Bool)
                    then
                      (if (((BitVec.join1 [(integer_access exp 0)]) == 0#1) : Bool)
                      then (BitVec.toNat (1#1 +++ (Sail.BitVec.extractLsb fraction 51 44)))
                      else (BitVec.toNat (0b01#2 +++ (Sail.BitVec.extractLsb fraction 51 45))))
                    else
                      (if (((BitVec.join1 [(integer_access exp 0)]) == 0#1) : Bool)
                      then (BitVec.toNat (1#1 +++ (Sail.BitVec.extractLsb fraction 51 41)))
                      else (BitVec.toNat (0b01#2 +++ (Sail.BitVec.extractLsb fraction 51 42))))
                  let scaled := scaled
                  let result_exp ← (( do (undefined_int ()) ) : SailM Int )
                  let result_exp : Int :=
                    match (Sail.BitVec.length result) with
                    | 16 => (fdiv_int (44 -i exp) 2)
                    | 32 => (fdiv_int (380 -i exp) 2)
                    | 64 => (fdiv_int (3068 -i exp) 2)
                    | _ => result_exp
                  let result_exp := result_exp
                  let estimate ← do (RecipSqrtEstimate scaled increasedprecision_name)
                  match (Sail.BitVec.length result) with
                  | 16 => (pure (((0#1 +++ (integer_subrange result_exp ((Sail.BitVec.length result) -i 12) 0)) +++ (integer_subrange estimate 7 0)) +++ (Zeros (n := 2))))
                  | 32 =>
                    (if ((! increasedprecision_name) : Bool)
                    then (pure (((0#1 +++ (integer_subrange result_exp ((Sail.BitVec.length result) -i 25) 0)) +++ (integer_subrange estimate 7 0)) +++ (Zeros (n := 15))))
                    else (pure (((0#1 +++ (integer_subrange result_exp ((Sail.BitVec.length result) -i 25) 0)) +++ (integer_subrange estimate 11 0)) +++ (Zeros (n := 11)))))
                  | 64 => (pure (((0#1 +++ (integer_subrange result_exp ((Sail.BitVec.length result) -i 54) 0)) +++ (integer_subrange estimate 7 0)) +++ (Zeros (n := 44))))
                  | _ => (pure result)))))

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPSub__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let result_sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length result) == 64))) "src/v8_base.sail:17770.41-17770.42"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1 fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2 fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs__1 type1 type2 op1 op2 fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let result ← (( do
        if (((inf1 && inf2) && (sign1 == sign2)) : Bool)
        then
          (do
            let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
            if (fpexc : Bool)
            then (FPProcessException FPExc_InvalidOp fpcr)
            else (pure ())
            (pure result))
        else
          (do
            if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 1#1))) : Bool)
            then (do (FPInfinity 0#1 (Sail.BitVec.length result)))
            else
              (do
                if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 0#1))) : Bool)
                then (do (FPInfinity 1#1 (Sail.BitVec.length result)))
                else
                  (do
                    if (((zero1 && zero2) && (sign1 == (Complement.complement sign2))) : Bool)
                    then (do (FPZero sign1 (Sail.BitVec.length result)))
                    else
                      (do
                        let result_value : real := (sub_real value1_name value2_name)
                        if ((eq_real result_value (0)) : Bool)
                        then
                          (do
                            let result_sign : (BitVec 1) :=
                              if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                              then 1#1
                              else 0#1
                            (FPZero result_sign (Sail.BitVec.length result)))
                        else (do (FPRound__2 result_value fpcr rounding fpexc (Sail.BitVec.length result))))))) ) : SailM (BitVec k_N) )
      if (fpexc : Bool)
      then (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
      else (pure ())
      (pure result))
  else (pure result)

/-- Type quantifiers: M : Nat, k_N : Nat, fbits : Int, k_is_unsigned : Bool, List.elem k_N [16, 32, 64] ∧ List.elem M [16, 32, 64] -/
def FPToFixed (op : (BitVec k_N)) (fbits : Int) (is_unsigned : Bool) (fpcr : (BitVec 64)) (rounding : FPRounding) (M : Nat) : SailM (BitVec M) := do
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let overflow ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector M) ) : SailM (BitVec M) )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:17844.41-17844.42"
  sail_assert ((M == 16) || ((M == 32) || (M == 64))) "src/v8_base.sail:17845.38-17845.39"
  sail_assert (fbits ≥b 0) "src/v8_base.sail:17846.21-17846.22"
  sail_assert (bne rounding FPRounding_ODD) "src/v8_base.sail:17847.37-17847.38"
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let (fptype, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op fpcr fpexc)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, value_name)) ) : SailM (FPType × real) )
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then (FPProcessException FPExc_InvalidOp fpcr)
  else (pure ())
  let value_name : real := (mult_real value_name (real_power (2) fbits))
  let int_result : Int := (round_down value_name)
  let error : real := (sub_real value_name (to_real int_result))
  let round_up ← (( do (undefined_bool ()) ) : SailM Bool )
  let round_up : Bool :=
    match rounding with
    | .FPRounding_TIEEVEN => ((gt_real error (1/2)) || ((eq_real error (1/2)) && ((BitVec.join1 [(integer_access int_result 0)]) == 1#1)))
    | .FPRounding_POSINF => (bne error (0))
    | .FPRounding_NEGINF => false
    | .FPRounding_ZERO => ((bne error (0)) && (int_result <b 0))
    | .FPRounding_TIEAWAY => ((gt_real error (1/2)) || ((eq_real error (1/2)) && (int_result ≥b 0)))
    | _ => round_up
  let int_result : Int :=
    if (round_up : Bool)
    then (int_result +i 1)
    else int_result
  let int_result := int_result
  let (overflow, result) ← (( do
    let (tup__0, tup__1) ← do (SatQ int_result M is_unsigned)
    let result : (BitVec M) := tup__0
    let overflow : Bool := tup__1
    (pure (overflow, result)) ) : SailM (Bool × (BitVec M)) )
  if (overflow : Bool)
  then (FPProcessException FPExc_InvalidOp fpcr)
  else
    (do
      if ((bne error (0)) : Bool)
      then (FPProcessException FPExc_Inexact fpcr)
      else (pure ()))
  (pure result)

/-- Type quantifiers: k_Is64 : Bool, k_M : Nat, N : Nat, k_M = 64 ∧ N = 32 -/
def FPToFixedJS (op : (BitVec k_M)) (fpcr : (BitVec 64)) (Is64 : Bool) (N : Nat) : SailM ((BitVec N) × (BitVec 1)) := do
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op) == 64) && (N == 32)) "src/v8_base.sail:17897.29-17897.30"
  let fpexc_idenorm ← (( do (pure (! ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1)))) ) : SailM Bool )
  let (fptype, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op fpcr fpexc_idenorm)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  let z : (BitVec 1) := 1#1
  let z ← (( do
    if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
    then
      (do
        (FPProcessException FPExc_InvalidOp fpcr)
        (pure 0#1))
    else (pure z) ) : SailM (BitVec 1) )
  let int_result : Int := (round_down value_name)
  let error : real := (sub_real value_name (to_real int_result))
  let round_it_up : Bool := ((bne error (0)) && (int_result <b 0))
  let int_result : Int :=
    if (round_it_up : Bool)
    then (int_result +i 1)
    else int_result
  let int_result := int_result
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let result : Int :=
    if ((int_result <b 0) : Bool)
    then (int_result -i ((2 ^i 32) *i (round_up (div_real (to_real int_result) (to_real (2 ^i 32))))))
    else (int_result -i ((2 ^i 32) *i (round_down (div_real (to_real int_result) (to_real (2 ^i 32))))))
  let z ← (( do
    if (((int_result <b (Neg.neg (2 ^i 31))) || (int_result >b ((2 ^i 31) -i 1))) : Bool)
    then
      (do
        (FPProcessException FPExc_InvalidOp fpcr)
        (pure 0#1))
    else
      (do
        if ((bne error (0)) : Bool)
        then
          (do
            (FPProcessException FPExc_Inexact fpcr)
            (pure 0#1))
        else
          (if (((sign == 1#1) && (eq_real value_name (0))) : Bool)
          then (pure 0#1)
          else
            (if ((((sign == 0#1) && (eq_real value_name (0))) && (! (IsZero (Sail.BitVec.extractLsb op 51 0)))) : Bool)
            then (pure 0#1)
            else (pure z)))) ) : SailM (BitVec 1) )
  let result : Int :=
    if ((BEq.beq fptype FPType_Infinity) : Bool)
    then 0
    else result
  let result := result
  (pure ((integer_subrange result (N -i 1) 0), z))

def CheckNonStreamingSVEEnabled (_ : Unit) : SailM Unit := do
  (CheckSVEEnabled ())
  if ((←((HaveSME ()) <&&> (do
       (pure ((← readReg PSTATE).SM == 1#1))) <&&> (do
       (pure (! (← (IsFullA64Enabled ()))))))) : Bool)
  then (SMEAccessTrap SMEExceptionType_Streaming (← readReg PSTATE).EL)
  else (pure ())

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPCompareUN (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM Bool := do
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:29873.41-29873.42"
  let type1 ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure type1) ) : SailM FPType )
  let type2 ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure type2) ) : SailM FPType )
  if (((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) : Bool)
  then (FPProcessException FPExc_InvalidOp fpcr)
  else (pure ())
  let result : Bool := (((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN)))
  if ((! result) : Bool)
  then (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
  else (pure ())
  (pure result)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPCompareNE (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM Bool := do
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:29896.41-29896.42"
  let result ← (( do (undefined_bool ()) ) : SailM Bool )
  let (type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (type1, value1_name)) ) : SailM (FPType × real) )
  let (type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (type2, value2_name)) ) : SailM (FPType × real) )
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  if ((op1_nan || op2_nan) : Bool)
  then
    (do
      let result : Bool := true
      if (((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) : Bool)
      then (FPProcessException FPExc_InvalidOp fpcr)
      else (pure ())
      (pure result))
  else
    (do
      let result : Bool := (bne value1_name value2_name)
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
      (pure result))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPLogB (op : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:31092.41-31092.42"
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let (fptype, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op fpcr)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, value_name)) ) : SailM (FPType × real) )
  let result ← (( do
    if ((((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) || (BEq.beq fptype FPType_Zero)) : Bool)
    then
      (do
        (FPProcessException FPExc_InvalidOp fpcr)
        (pure (Neg.neg (2 ^i ((Sail.BitVec.length op) -i 1)))))
    else
      (do
        if ((BEq.beq fptype FPType_Infinity) : Bool)
        then (pure ((2 ^i ((Sail.BitVec.length op) -i 1)) -i 1))
        else
          (do
            let value_name : real := (abs_real value_name)
            let result : Int := 0
            let (result, value_name) ← (( do
              let mut loop_vars := (result, value_name)
              while (λ (result, value_name) => (lt_real value_name (1))) loop_vars do
                let (result, value_name) := loop_vars
                loop_vars :=
                  (let value_name : real := (mult_real value_name (2))
                  let result : Int := (result -i 1)
                  (result, value_name) : (Int × real))
              (pure loop_vars) ) : SailM (Int × real) )
            let (result, value_name) ← (( do
              let mut loop_vars_1 := (result, value_name)
              while (λ (result, value_name) => (gteq_real value_name (2))) loop_vars_1 do
                let (result, value_name) := loop_vars_1
                loop_vars_1 :=
                  (let value_name : real := (div_real value_name (2))
                  let result : Int := (result +i 1)
                  (result, value_name) : (Int × real))
              (pure loop_vars_1) ) : SailM (Int × real) )
            (FPProcessDenorm fptype (Sail.BitVec.length op) fpcr)
            (pure result))) ) : SailM Int )
  let result := result
  (pure (integer_subrange result ((Sail.BitVec.length op) -i 1) 0))

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPConvertBF (op : (BitVec k_N)) (fpcr_in : (BitVec 64)) (rounding_in : FPRounding) : SailM (BitVec (k_N / 2)) := do
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert ((Sail.BitVec.length op) == 32) "src/v8_base.sail:32225.19-32225.20"
  let halfsize := (Int.ediv (Sail.BitVec.length op) 2)
  let fpcr : FPCRType := fpcr_in
  let rounding : FPRounding := rounding_in
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op)) ) : SailM (BitVec k_N) )
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let rounding : FPRounding :=
    if (altfp : Bool)
    then FPRounding_TIEEVEN
    else rounding
  let (fptype, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op fpcr fpexc)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  let result ← (( do
    if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
    then
      (do
        let result ← (( do
          if (((_get_FPCRType_DN fpcr) == 1#1) : Bool)
          then (do (FPDefaultNaN__1 fpcr (Sail.BitVec.length result)))
          else (do (FPConvertNaN op (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
        if ((BEq.beq fptype FPType_SNaN) : Bool)
        then
          (do
            if (fpexc : Bool)
            then (FPProcessException FPExc_InvalidOp fpcr)
            else (pure ()))
        else (pure ())
        (pure result))
    else
      (do
        if ((BEq.beq fptype FPType_Infinity) : Bool)
        then (do (FPInfinity sign (Sail.BitVec.length result)))
        else
          (do
            if ((BEq.beq fptype FPType_Zero) : Bool)
            then (do (FPZero sign (Sail.BitVec.length result)))
            else (do (FPRoundBF value_name fpcr rounding fpexc (Sail.BitVec.length result))))) ) : SailM (BitVec k_N) )
  (pure (Sail.BitVec.extractLsb result ((2 *i halfsize) -i 1) halfsize))

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 16 -/
def BFAdd__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result_sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert ((Sail.BitVec.length op2) == 16) "src/v8_base.sail:32512.19-32512.20"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (2 *i (Sail.BitVec.length op2))) ) : SailM (BitVec (2 * k_N)) )
  let op1_s : (BitVec (2 * k_N)) := (op1 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let op2_s : (BitVec (2 * k_N)) := (op2 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1_s fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2_s fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs__1 type1 type2 op1_s op2_s fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec (2 * k_N)) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec (2 * k_N))) )
  let result ← (( do
    if ((! done) : Bool)
    then
      (do
        let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
        let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
        let zero1 : Bool := (BEq.beq type1 FPType_Zero)
        let zero2 : Bool := (BEq.beq type2 FPType_Zero)
        let result ← (( do
          if (((inf1 && inf2) && (sign1 == (Complement.complement sign2))) : Bool)
          then
            (do
              let result ← (FPDefaultNaN__1 fpcr (2 *i (Sail.BitVec.length op2)))
              if (fpexc : Bool)
              then (FPProcessException FPExc_InvalidOp fpcr)
              else (pure ())
              (pure result))
          else
            (do
              if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 0#1))) : Bool)
              then (do (FPInfinity 0#1 (2 *i (Sail.BitVec.length op2))))
              else
                (do
                  if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 1#1))) : Bool)
                  then (do (FPInfinity 1#1 (2 *i (Sail.BitVec.length op2))))
                  else
                    (do
                      if (((zero1 && zero2) && (sign1 == sign2)) : Bool)
                      then (do (FPZero sign1 (2 *i (Sail.BitVec.length op2))))
                      else
                        (do
                          let result_value : real := (add_real value1_name value2_name)
                          if ((eq_real result_value (0)) : Bool)
                          then
                            (do
                              let result_sign : (BitVec 1) :=
                                if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                                then 1#1
                                else 0#1
                              (FPZero result_sign (2 *i (Sail.BitVec.length op2))))
                          else (do (FPRoundBF result_value fpcr rounding fpexc (2 *i (Sail.BitVec.length op2)))))))) ) : SailM (BitVec (2 * k_N)) )
        if (fpexc : Bool)
        then (FPProcessDenorms type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr)
        else (pure ())
        (pure result))
    else (pure result) ) : SailM (BitVec (2 * k_N)) )
  (pure (Sail.BitVec.extractLsb result ((2 *i (Sail.BitVec.length op2)) -i 1) (Sail.BitVec.length op2)))

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 16 -/
def BFSub__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result_sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert ((Sail.BitVec.length op2) == 16) "src/v8_base.sail:32590.19-32590.20"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (2 *i (Sail.BitVec.length op2))) ) : SailM (BitVec (2 * k_N)) )
  let op1_s : (BitVec (2 * k_N)) := (op1 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let op2_s : (BitVec (2 * k_N)) := (op2 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1_s fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2_s fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs__1 type1 type2 op1_s op2_s fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec (2 * k_N)) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec (2 * k_N))) )
  let result ← (( do
    if ((! done) : Bool)
    then
      (do
        let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
        let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
        let zero1 : Bool := (BEq.beq type1 FPType_Zero)
        let zero2 : Bool := (BEq.beq type2 FPType_Zero)
        let result ← (( do
          if (((inf1 && inf2) && (sign1 == sign2)) : Bool)
          then
            (do
              let result ← (FPDefaultNaN__1 fpcr (2 *i (Sail.BitVec.length op2)))
              if (fpexc : Bool)
              then (FPProcessException FPExc_InvalidOp fpcr)
              else (pure ())
              (pure result))
          else
            (do
              if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 1#1))) : Bool)
              then (do (FPInfinity 0#1 (2 *i (Sail.BitVec.length op2))))
              else
                (do
                  if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 0#1))) : Bool)
                  then (do (FPInfinity 1#1 (2 *i (Sail.BitVec.length op2))))
                  else
                    (do
                      if (((zero1 && zero2) && (sign1 == (Complement.complement sign2))) : Bool)
                      then (do (FPZero sign1 (2 *i (Sail.BitVec.length op2))))
                      else
                        (do
                          let result_value : real := (sub_real value1_name value2_name)
                          if ((eq_real result_value (0)) : Bool)
                          then
                            (do
                              let result_sign : (BitVec 1) :=
                                if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                                then 1#1
                                else 0#1
                              (FPZero result_sign (2 *i (Sail.BitVec.length op2))))
                          else (do (FPRoundBF result_value fpcr rounding fpexc (2 *i (Sail.BitVec.length op2)))))))) ) : SailM (BitVec (2 * k_N)) )
        if (fpexc : Bool)
        then (FPProcessDenorms type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr)
        else (pure ())
        (pure result))
    else (pure result) ) : SailM (BitVec (2 * k_N)) )
  (pure (Sail.BitVec.extractLsb result ((2 *i (Sail.BitVec.length op2)) -i 1) (Sail.BitVec.length op2)))

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 16 -/
def BFMulAdd__1 (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let infA ← (( do (undefined_bool ()) ) : SailM Bool )
  let infP ← (( do (undefined_bool ()) ) : SailM Bool )
  let invalidop ← (( do (undefined_bool ()) ) : SailM Bool )
  let result_sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let signA ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let signP ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let typeA ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let valueA_name ← (( do (undefined_real ()) ) : SailM real )
  let zeroA ← (( do (undefined_bool ()) ) : SailM Bool )
  let zeroP ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert ((Sail.BitVec.length op2) == 16) "src/v8_base.sail:32674.19-32674.20"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (2 *i (Sail.BitVec.length op2))) ) : SailM (BitVec (2 * k_N)) )
  let addend_s : (BitVec (2 * k_N)) := (addend +++ (Zeros (n := (Sail.BitVec.length op2))))
  let op1_s : (BitVec (2 * k_N)) := (op1 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let op2_s : (BitVec (2 * k_N)) := (op2 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let (signA, typeA, valueA_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 addend_s fpcr fpexc)
    let typeA : FPType := tup__0
    let signA : (BitVec 1) := tup__1
    let valueA_name : real := tup__2
    (pure (signA, typeA, valueA_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1_s fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2_s fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
  let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
  let zero1 : Bool := (BEq.beq type1 FPType_Zero)
  let zero2 : Bool := (BEq.beq type2 FPType_Zero)
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs3__1 typeA type1 type2 addend_s op1_s op2_s fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec (2 * k_N)) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec (2 * k_N))) )
  let result ← (( do
    if ((! ((←((HaveAltFP ()) <&&> (do
             (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) : Bool)
    then
      (do
        if (((BEq.beq typeA FPType_QNaN) && ((inf1 && zero2) || (zero1 && inf2))) : Bool)
        then
          (do
            let result ← (FPDefaultNaN__1 fpcr (2 *i (Sail.BitVec.length op2)))
            if (fpexc : Bool)
            then (FPProcessException FPExc_InvalidOp fpcr)
            else (pure ())
            (pure result))
        else (pure result))
    else (pure result) ) : SailM (BitVec (2 * k_N)) )
  let result ← (( do
    if ((! done) : Bool)
    then
      (do
        let infA : Bool := (BEq.beq typeA FPType_Infinity)
        let zeroA : Bool := (BEq.beq typeA FPType_Zero)
        let signP : (BitVec 1) := (sign1 ^^^ sign2)
        let infP : Bool := (inf1 || inf2)
        let zeroP : Bool := (zero1 || zero2)
        let invalidop : Bool := (((inf1 && zero2) || (zero1 && inf2)) || ((infA && infP) && (signA != signP)))
        let result ← (( do
          if (invalidop : Bool)
          then
            (do
              let result ← (FPDefaultNaN__1 fpcr (2 *i (Sail.BitVec.length op2)))
              if (fpexc : Bool)
              then (FPProcessException FPExc_InvalidOp fpcr)
              else (pure ())
              (pure result))
          else
            (do
              if (((infA && (signA == 0#1)) || (infP && (signP == 0#1))) : Bool)
              then (do (FPInfinity 0#1 (2 *i (Sail.BitVec.length op2))))
              else
                (do
                  if (((infA && (signA == 1#1)) || (infP && (signP == 1#1))) : Bool)
                  then (do (FPInfinity 1#1 (2 *i (Sail.BitVec.length op2))))
                  else
                    (do
                      if (((zeroA && zeroP) && (signA == signP)) : Bool)
                      then (do (FPZero signA (2 *i (Sail.BitVec.length op2))))
                      else
                        (do
                          let result_value : real := (add_real valueA_name (mult_real value1_name value2_name))
                          if ((eq_real result_value (0)) : Bool)
                          then
                            (do
                              let result_sign : (BitVec 1) :=
                                if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                                then 1#1
                                else 0#1
                              (FPZero result_sign (2 *i (Sail.BitVec.length op2))))
                          else (do (FPRoundBF result_value fpcr rounding fpexc (2 *i (Sail.BitVec.length op2)))))))) ) : SailM (BitVec (2 * k_N)) )
        if (((! invalidop) && fpexc) : Bool)
        then (FPProcessDenorms3 typeA type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr)
        else (pure ())
        (pure result))
    else (pure result) ) : SailM (BitVec (2 * k_N)) )
  (pure (Sail.BitVec.extractLsb result ((2 *i (Sail.BitVec.length op2)) -i 1) (Sail.BitVec.length op2)))

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 16 -/
def BFMul__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert ((Sail.BitVec.length op2) == 16) "src/v8_base.sail:32769.19-32769.20"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (2 *i (Sail.BitVec.length op2))) ) : SailM (BitVec (2 * k_N)) )
  let op1_s : (BitVec (2 * k_N)) := (op1 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let op2_s : (BitVec (2 * k_N)) := (op2 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1_s fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2_s fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs__1 type1 type2 op1_s op2_s fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec (2 * k_N)) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec (2 * k_N))) )
  let result ← (( do
    if ((! done) : Bool)
    then
      (do
        let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
        let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
        let zero1 : Bool := (BEq.beq type1 FPType_Zero)
        let zero2 : Bool := (BEq.beq type2 FPType_Zero)
        let result ← (( do
          if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
          then
            (do
              let result ← (FPDefaultNaN__1 fpcr (2 *i (Sail.BitVec.length op2)))
              if (fpexc : Bool)
              then (FPProcessException FPExc_InvalidOp fpcr)
              else (pure ())
              (pure result))
          else
            (do
              if ((inf1 || inf2) : Bool)
              then (do (FPInfinity (sign1 ^^^ sign2) (2 *i (Sail.BitVec.length op2))))
              else
                (do
                  if ((zero1 || zero2) : Bool)
                  then (do (FPZero (sign1 ^^^ sign2) (2 *i (Sail.BitVec.length op2))))
                  else (do (FPRoundBF (mult_real value1_name value2_name) fpcr rounding fpexc (2 *i (Sail.BitVec.length op2)))))) ) : SailM (BitVec (2 * k_N)) )
        if (fpexc : Bool)
        then (FPProcessDenorms type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr)
        else (pure ())
        (pure result))
    else (pure result) ) : SailM (BitVec (2 * k_N)) )
  (pure (Sail.BitVec.extractLsb result ((2 *i (Sail.BitVec.length op2)) -i 1) (Sail.BitVec.length op2)))

/-- Type quantifiers: k_N : Nat, k_altfp : Bool, k_N = 16 -/
def BFMin__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) (altfp : Bool) : SailM (BitVec k_N) := do
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert ((Sail.BitVec.length op2) == 16) "src/v8_base.sail:32821.19-32821.20"
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := true
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (2 *i (Sail.BitVec.length op2))) ) : SailM (BitVec (2 * k_N)) )
  let op1_s : (BitVec (2 * k_N)) := (op1 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let op2_s : (BitVec (2 * k_N)) := (op2 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1_s fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2_s fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  if ((((altfp && (BEq.beq type1 FPType_Zero)) && (BEq.beq type2 FPType_Zero)) && (sign1 != sign2)) : Bool)
  then (BFZero sign2 (Sail.BitVec.length op2))
  else
    (do
      if ((altfp && (((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN)))) : Bool)
      then
        (do
          (FPProcessException FPExc_InvalidOp fpcr)
          if ((BEq.beq type2 FPType_Zero) : Bool)
          then (BFZero sign2 (Sail.BitVec.length op2))
          else (pure op2))
      else
        (do
          let (done, result) ← (( do
            let (tup__0, tup__1) ← do (FPProcessNaNs type1 type2 op1_s op2_s fpcr)
            let done : Bool := tup__0
            let result : (BitVec (2 * k_N)) := tup__1
            (pure (done, result)) ) : SailM (Bool × (BitVec (2 * k_N))) )
          let result ← (( do
            if ((! done) : Bool)
            then
              (do
                let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
                let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
                let value_name ← (( do (undefined_real ()) ) : SailM real )
                let (fptype, sign, value_name) : (FPType × (BitVec 1) × real) :=
                  if ((lt_real value1_name value2_name) : Bool)
                  then
                    (let (tup__0, tup__1, tup__2) := ((type1, sign1, value1_name) : (FPType × (BitVec 1) × real))
                    let fptype : FPType := tup__0
                    let sign : (BitVec 1) := tup__1
                    let value_name : real := tup__2
                    (fptype, sign, value_name))
                  else
                    (let (tup__0, tup__1, tup__2) := ((type2, sign2, value2_name) : (FPType × (BitVec 1) × real))
                    let fptype : FPType := tup__0
                    let sign : (BitVec 1) := tup__1
                    let value_name : real := tup__2
                    (fptype, sign, value_name))
                let (fpcr, result) ← (( do
                  if ((BEq.beq fptype FPType_Infinity) : Bool)
                  then
                    (do
                      let result ← (FPInfinity sign (2 *i (Sail.BitVec.length op2)))
                      (pure (fpcr, result)))
                  else
                    (do
                      let (fpcr, result) ← (( do
                        if ((BEq.beq fptype FPType_Zero) : Bool)
                        then
                          (do
                            let sign : (BitVec 1) := (sign1 ||| sign2)
                            let result ← (FPZero sign (2 *i (Sail.BitVec.length op2)))
                            (pure (fpcr, result)))
                        else
                          (do
                            let fpcr : (BitVec 64) :=
                              if (altfp : Bool)
                              then (Sail.BitVec.updateSubrange fpcr 24 24 0#1)
                              else fpcr
                            let result ← (FPRoundBF value_name fpcr rounding fpexc (2 *i (Sail.BitVec.length op2)))
                            (pure (fpcr, result))) ) : SailM ((BitVec 64) × (BitVec (2 * k_N))) )
                      (pure (fpcr, result))) ) : SailM ((BitVec 64) × (BitVec (2 * k_N))) )
                if (fpexc : Bool)
                then (FPProcessDenorms type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr)
                else (pure ())
                (pure result))
            else (pure result) ) : SailM (BitVec (2 * k_N)) )
          (pure (Sail.BitVec.extractLsb result ((2 *i (Sail.BitVec.length op2)) -i 1) (Sail.BitVec.length op2)))))

/-- Type quantifiers: k_N : Nat, k_altfp : Bool, k_N = 16 -/
def BFMax__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) (altfp : Bool) : SailM (BitVec k_N) := do
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert ((Sail.BitVec.length op2) == 16) "src/v8_base.sail:32918.19-32918.20"
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := true
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (2 *i (Sail.BitVec.length op2))) ) : SailM (BitVec (2 * k_N)) )
  let op1_s : (BitVec (2 * k_N)) := (op1 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let op2_s : (BitVec (2 * k_N)) := (op2 +++ (Zeros (n := (Sail.BitVec.length op2))))
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1_s fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2_s fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  if ((((altfp && (BEq.beq type1 FPType_Zero)) && (BEq.beq type2 FPType_Zero)) && (sign1 != sign2)) : Bool)
  then (BFZero sign2 (Sail.BitVec.length op2))
  else
    (do
      if ((altfp && (((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN)))) : Bool)
      then
        (do
          (FPProcessException FPExc_InvalidOp fpcr)
          if ((BEq.beq type2 FPType_Zero) : Bool)
          then (BFZero sign2 (Sail.BitVec.length op2))
          else (pure op2))
      else
        (do
          let (done, result) ← (( do
            let (tup__0, tup__1) ← do (FPProcessNaNs type1 type2 op1_s op2_s fpcr)
            let done : Bool := tup__0
            let result : (BitVec (2 * k_N)) := tup__1
            (pure (done, result)) ) : SailM (Bool × (BitVec (2 * k_N))) )
          let result ← (( do
            if ((! done) : Bool)
            then
              (do
                let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
                let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
                let value_name ← (( do (undefined_real ()) ) : SailM real )
                let (fptype, sign, value_name) : (FPType × (BitVec 1) × real) :=
                  if ((gt_real value1_name value2_name) : Bool)
                  then
                    (let (tup__0, tup__1, tup__2) := ((type1, sign1, value1_name) : (FPType × (BitVec 1) × real))
                    let fptype : FPType := tup__0
                    let sign : (BitVec 1) := tup__1
                    let value_name : real := tup__2
                    (fptype, sign, value_name))
                  else
                    (let (tup__0, tup__1, tup__2) := ((type2, sign2, value2_name) : (FPType × (BitVec 1) × real))
                    let fptype : FPType := tup__0
                    let sign : (BitVec 1) := tup__1
                    let value_name : real := tup__2
                    (fptype, sign, value_name))
                let (fpcr, result) ← (( do
                  if ((BEq.beq fptype FPType_Infinity) : Bool)
                  then
                    (do
                      let result ← (FPInfinity sign (2 *i (Sail.BitVec.length op2)))
                      (pure (fpcr, result)))
                  else
                    (do
                      let (fpcr, result) ← (( do
                        if ((BEq.beq fptype FPType_Zero) : Bool)
                        then
                          (do
                            let sign : (BitVec 1) := (sign1 &&& sign2)
                            let result ← (FPZero sign (2 *i (Sail.BitVec.length op2)))
                            (pure (fpcr, result)))
                        else
                          (do
                            let fpcr : (BitVec 64) :=
                              if (altfp : Bool)
                              then (Sail.BitVec.updateSubrange fpcr 24 24 0#1)
                              else fpcr
                            let result ← (FPRoundBF value_name fpcr rounding fpexc (2 *i (Sail.BitVec.length op2)))
                            (pure (fpcr, result))) ) : SailM ((BitVec 64) × (BitVec (2 * k_N))) )
                      (pure (fpcr, result))) ) : SailM ((BitVec 64) × (BitVec (2 * k_N))) )
                if (fpexc : Bool)
                then (FPProcessDenorms type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr)
                else (pure ())
                (pure result))
            else (pure result) ) : SailM (BitVec (2 * k_N)) )
          (pure (Sail.BitVec.extractLsb result ((2 *i (Sail.BitVec.length op2)) -i 1) (Sail.BitVec.length op2)))))

/-- Type quantifiers: k_cold_reset : Bool -/
def AArch64_TakeReset (cold_reset : Bool) : SailM Unit := do
  sail_assert (← (HaveAArch64 ())) "src/v8_base.sail:33499.24-33499.25"
  writeReg PSTATE { (← readReg PSTATE) with nRW := 0#1 }
  if ((HaveEL EL3) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with EL := EL3 }
  else
    (do
      if ((HaveEL EL2) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with EL := EL2 }
      else writeReg PSTATE { (← readReg PSTATE) with EL := EL1 })
  (AArch64_ResetControlRegisters cold_reset)
  writeReg PSTATE { (← readReg PSTATE) with SP := 1#1 }
  writeReg PSTATE { (← readReg PSTATE) with D := (Sail.BitVec.extractLsb 0b1111#4 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with A := (Sail.BitVec.extractLsb 0b1111#4 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb 0b1111#4 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb 0b1111#4 0 0) }
  writeReg PSTATE { (← readReg PSTATE) with SS := 0#1 }
  writeReg PSTATE { (← readReg PSTATE) with DIT := 0#1 }
  writeReg PSTATE { (← readReg PSTATE) with IL := 0#1 }
  if ((← (HaveTME ())) : Bool)
  then writeReg TSTATE { (← readReg TSTATE) with depth := 0 }
  else (pure ())
  (AArch64_ResetGeneralRegisters ())
  (AArch64_ResetSIMDFPRegisters ())
  (AArch64_ResetSpecialRegisters ())
  (ResetExternalDebugRegisters cold_reset)
  let rv ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let rv ← (( do
    if ((HaveEL EL3) : Bool)
    then (do readReg RVBAR_EL3)
    else
      (do
        if ((HaveEL EL2) : Bool)
        then (do readReg RVBAR_EL2)
        else (do readReg RVBAR_EL1)) ) : SailM (BitVec 64) )
  sail_assert ((is_zero_subrange rv 63 (← (AArch64_PAMax ()))) && (IsZero (Sail.BitVec.extractLsb rv 1 0))) "src/v8_base.sail:33529.73-33529.74"
  let branch_conditional : Bool := false
  (BranchTo rv BranchType_RESET branch_conditional)

def CheckFPAdvSIMDEnabled64 (_ : Unit) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())

def SPEPreExecution (_ : Unit) : SailM Unit := do
  if ((← (StatisticalProfilingEnabled ())) : Bool)
  then
    (do
      (PMUEvent PMU_EVENT_SAMPLE_POP)
      if ((← (SPEToCollectSample ())) : Bool)
      then
        (do
          if ((! (← readReg SPESampleInFlight)) : Bool)
          then
            (do
              writeReg SPESampleInFlight true
              (SPEStartCounter SPECounterPosTotalLatency)
              (SPEStartCounter SPECounterPosIssueLatency)
              (SPESampleAddContext ())
              (SPESampleAddAddressPCVirtual ())
              (SPESampleAddTimeStamp ()))
          else
            (do
              (PMUEvent PMU_EVENT_SAMPLE_COLLISION)
              writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange (← readReg PMBSR_EL1) 16 16 1#1))
          (SPESampleAddOpOther__1 false))
      else (pure ()))
  else (pure ())

def DRPSInstruction (_ : Unit) : SailM Unit := do
  let _ : Unit := (SynchronizeContext ())
  let sync_errors ← (( do (HaveIESB ()) <&&> (do (pure ((_get_SCTLRType_IESB (← (SCTLR_read__1 ()))) == 1#1))) ) : SailM Bool )
  let sync_errors ← (( do
    if ((←((HaveDoubleFaultExt ()) <&&> (do
         (pure (! (← (UsingAArch32 ()))))))) : Bool)
    then (do (pure sync_errors) <||> (do (pure ((← (EffectiveEA ())) == 1#1)) <&&> (do (pure ((_get_SCR_EL3_Type_NMEA (← readReg SCR_EL3)) == 1#1))) <&&> (do (pure ((← readReg PSTATE).EL == EL3)))))
    else (pure sync_errors) ) : SailM Bool )
  let sync_errors ← (( do
    if ((! (← (ConstrainUnpredictableBool Unpredictable_IESBinDebug))) : Bool)
    then (pure false)
    else (pure sync_errors) ) : SailM Bool )
  let _ : Unit :=
    if (sync_errors : Bool)
    then (SynchronizeErrors ())
    else ()
  (DebugRestorePSR ())

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV87 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap7_IMPLEMENTED enabled
  if (enabled : Bool)
  then (__ConfigureV86 enabled)
  else (pure ())

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV91 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap1_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV90 enabled)
      (__ConfigureV86 enabled))
  else (pure ())

/-- Type quantifiers: k_advsimd : Bool, k_fpexc_check : Bool -/
def AArch32_CheckAdvSIMDOrFPEnabled (fpexc_check : Bool) (advsimd : Bool) : SailM Unit := do
  let cpacr_asedis ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let cpacr_cp10 ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let fpexc_en ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <&&> (do
       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
       (pure (! (← (EL2Enabled ())))) <||> (do
         (pure (! (← (ELUsingAArch32 EL2)))) <&&> (do
           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1))))))) : Bool)
  then
    (do
      (AArch64_CheckFPEnabled ())
      (AArch64_CheckFPAdvSIMDEnabled ()))
  else
    (do
      if ((←((pure ((← readReg PSTATE).EL == EL0)) <&&> (do
           (EL2Enabled ())) <&&> (do
           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))) <&&> (do
           (pure (! (← (ELUsingAArch32 EL1))))))) : Bool)
      then
        (do
          if ((←((pure fpexc_check) <&&> (do
               (pure ((_get_HCR_EL2_Type_RW (← readReg HCR_EL2)) == 0#1))))) : Bool)
          then
            (do
              let fpexc_en ← (( do (__IMPDEF_bits 1 "FPEXC.EN value when TGE==1 and RW==0") ) : SailM (BitVec 1) )
              if ((fpexc_en == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ()))
          else (pure ())
          (AArch64_CheckFPEnabled ()))
      else
        (do
          let cpacr_asedis ← (( do (pure (_get_CPACR_Type_ASEDIS (← (CPACR_read__1 ())))) ) : SailM (BitVec 1) )
          let cpacr_cp10 ← (( do (pure (_get_CPACR_Type_cp10 (← (CPACR_read__1 ())))) ) : SailM (BitVec 2) )
          let (cpacr_asedis, cpacr_cp10) ← (( do
            if ((←((pure (HaveEL EL3)) <&&> (do
                 (ELUsingAArch32 EL3)) <&&> (do
                 (pure (BEq.beq (← (CurrentSecurityState ())) SS_NonSecure))))) : Bool)
            then
              (do
                let cpacr_asedis ← (( do
                  if (((_get_NSACR_Type_NSASEDIS (← readReg NSACR)) == 1#1) : Bool)
                  then (pure 1#1)
                  else (pure cpacr_asedis) ) : SailM (BitVec 1) )
                let cpacr_cp10 ← (( do
                  if (((_get_NSACR_Type_cp10 (← readReg NSACR)) == 0#1) : Bool)
                  then (pure 0b00#2)
                  else (pure cpacr_cp10) ) : SailM (BitVec 2) )
                (pure (cpacr_asedis, cpacr_cp10)))
            else (pure (cpacr_asedis, cpacr_cp10)) ) : SailM ((BitVec 1) × (BitVec 2)) )
          if (((← readReg PSTATE).EL != EL2) : Bool)
          then
            (do
              if ((advsimd && (cpacr_asedis == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let disabled ← (( do (undefined_bool ()) ) : SailM Bool )
              let disabled ← (( do
                match (cpacr_cp10 : BitVec 2) with
                | 0b00 => (pure true)
                | 0b01 => (do (pure ((← readReg PSTATE).EL == EL0)))
                | 0b10 => (do (ConstrainUnpredictableBool Unpredictable_RESCPACR))
                | _ => (pure false) ) : SailM Bool )
              let disabled := disabled
              if (disabled : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ()))
          else (pure ())
          if ((←((pure fpexc_check) <&&> (do
               (pure ((_get_FPEXC_Type_EN (← (FPEXC_read ()))) == 0#1))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (pure ())
          (AArch32_CheckFPAdvSIMDTrap advsimd)))

def ALUExceptionReturn (address : (BitVec 32)) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure ((← readReg PSTATE).M == M32_User)) <||> (do
           (pure ((← readReg PSTATE).M == M32_System))))) : Bool)
      then
        (do
          let c ← (( do (ConstrainUnpredictable Unpredictable_ALUEXCEPTIONRETURN) ) : SailM Constraint )
          sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/v8_base.sail:42343.58-42343.59"
          match c with
          | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
          | .Constraint_NOP => (EndOfInstruction ())
          | _ => (pure ()))
      else (AArch32_ExceptionReturn address (← (SPSR_read (N := 32)))))

/-- Type quantifiers: k_cold_reset : Bool -/
def AArch32_TakeReset (cold_reset : Bool) : SailM Unit := do
  sail_assert (! (← (HaveAArch64 ()))) "src/v8_base.sail:42835.34-42835.35"
  if ((HaveEL EL3) : Bool)
  then
    (do
      (AArch32_WriteMode M32_Svc)
      writeReg SCR (Sail.BitVec.updateSubrange (← readReg SCR) 0 0 0#1))
  else
    (do
      if ((HaveEL EL2) : Bool)
      then (AArch32_WriteMode M32_Hyp)
      else (AArch32_WriteMode M32_Svc))
  (AArch32_ResetControlRegisters cold_reset)
  (FPEXC_write (_update_FPEXC_Type_EN (← (FPEXC_read ())) 0#1))
  writeReg PSTATE { (← readReg PSTATE) with A := (Sail.BitVec.extractLsb 0b111#3 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb 0b111#3 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb 0b111#3 0 0) }
  writeReg PSTATE { (← readReg PSTATE) with IT := 0b00000000#8 }
  if (((HaveEL EL2) && (! (HaveEL EL3))) : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with T := ← (do (pure (_get_HSCTLR_Type_TE (← (HSCTLR_read ()))))) }
      writeReg PSTATE { (← readReg PSTATE) with E := ← (do (pure (_get_HSCTLR_Type_EE (← (HSCTLR_read ()))))) })
  else
    (do
      writeReg PSTATE { (← readReg PSTATE) with T := ← (do (pure (_get_SCTLR_Type_TE (← (SCTLR_read__2 ()))))) }
      writeReg PSTATE { (← readReg PSTATE) with E := ← (do (pure (_get_SCTLR_Type_EE (← (SCTLR_read__2 ()))))) })
  writeReg PSTATE { (← readReg PSTATE) with IL := 0#1 }
  (AArch32_ResetGeneralRegisters ())
  (AArch32_ResetSIMDFPRegisters ())
  (AArch32_ResetSpecialRegisters ())
  (ResetExternalDebugRegisters cold_reset)
  let rv ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let rv ← (( do
    if ((HaveEL EL3) : Bool)
    then
      (do
        if (((BitVec.join1 [(BitVec.access (← readReg MVBAR) 0)]) == 1#1) : Bool)
        then (do (pure ((Sail.BitVec.extractLsb (← readReg MVBAR) 31 1) +++ 0#1)))
        else (do (__IMPDEF_bits 32 "reset vector address")))
    else (do (pure ((Sail.BitVec.extractLsb (← readReg RVBAR) 31 1) +++ 0#1))) ) : SailM (BitVec 32) )
  sail_assert (←((pure ((BitVec.join1 [(BitVec.access rv 0)]) == 0#1)) <&&> (do
    (pure (((← readReg PSTATE).T == 1#1) || ((BitVec.join1 [(BitVec.access rv 1)]) == 0#1)))))) "src/v8_base.sail:42870.62-42870.63"
  let branch_conditional : Bool := false
  (BranchTo rv BranchType_RESET branch_conditional)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPAdd (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (FPAdd__1 op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPAdd_ZA (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := false
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  (FPAdd__1 op1 op2 fpcr fpexc)

/-- Type quantifiers: M : Nat, k_N : Nat, List.elem M [16, 32, 64] ∧ List.elem k_N [16, 32, 64] -/
def FPConvert__1 (op : (BitVec k_N)) (fpcr : (BitVec 64)) (M : Nat) : SailM (BitVec M) := do
  (FPConvert op fpcr (← (FPRoundingMode fpcr)) M)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPDiv (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length result) == 64))) "src/v8_base.sail:16583.41-16583.42"
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs type1 type2 op1 op2 fpcr)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let result ← (( do
        if (((inf1 && inf2) || (zero1 && zero2)) : Bool)
        then
          (do
            let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
            (FPProcessException FPExc_InvalidOp fpcr)
            (pure result))
        else
          (do
            if ((inf1 || zero2) : Bool)
            then
              (do
                let result ← (FPInfinity (sign1 ^^^ sign2) (Sail.BitVec.length result))
                if ((! inf1) : Bool)
                then (FPProcessException FPExc_DivideByZero fpcr)
                else (pure ())
                (pure result))
            else
              (do
                if ((zero1 || inf2) : Bool)
                then (do (FPZero (sign1 ^^^ sign2) (Sail.BitVec.length result)))
                else (do (FPRound (div_real value1_name value2_name) fpcr (Sail.BitVec.length result))))) ) : SailM (BitVec k_N) )
      if ((! zero2) : Bool)
      then (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
      else (pure ())
      (pure result))
  else (pure result)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMax (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  (FPMax__1 op1 op2 fpcr altfp)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMaxNum (op1_in : (BitVec k_N)) (op2_in : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  sail_assert (((Sail.BitVec.length op2_in) == 16) || (((Sail.BitVec.length op2_in) == 32) || ((Sail.BitVec.length op2_in) == 64))) "src/v8_base.sail:16680.41-16680.42"
  let op1 : (BitVec k_N) := op1_in
  let op2 : (BitVec k_N) := op2_in
  let type1 ← (( do
    let (__tup_0, _, _) ← do (FPUnpack op1 fpcr)
    (pure __tup_0) ) : SailM FPType )
  let type2 ← (( do
    let (__tup_0, _, _) ← do (FPUnpack op2 fpcr)
    (pure __tup_0) ) : SailM FPType )
  let type1_nan : Bool := ((BEq.beq type1 FPType_QNaN) || (BEq.beq type1 FPType_SNaN))
  let type2_nan : Bool := ((BEq.beq type2 FPType_QNaN) || (BEq.beq type2 FPType_SNaN))
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let (op1, op2) ← (( do
    if ((! ((altfp && type1_nan) && type2_nan)) : Bool)
    then
      (do
        let (op1, op2) ← (( do
          if (((BEq.beq type1 FPType_QNaN) && (bne type2 FPType_QNaN)) : Bool)
          then
            (do
              let op1 ← (FPInfinity 1#1 (Sail.BitVec.length op2_in))
              (pure (op1, op2)))
          else
            (do
              let op2 ← (( do
                if (((bne type1 FPType_QNaN) && (BEq.beq type2 FPType_QNaN)) : Bool)
                then (do (FPInfinity 1#1 (Sail.BitVec.length op2_in)))
                else (pure op2) ) : SailM (BitVec k_N) )
              (pure (op1, op2))) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
        (pure (op1, op2)))
    else (pure (op1, op2)) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
  let altfmaxfmin : Bool := false
  (FPMax__1 op1 op2 fpcr altfmaxfmin)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMin (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  (FPMin__1 op1 op2 fpcr altfp)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMinNum (op1_in : (BitVec k_N)) (op2_in : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  sail_assert (((Sail.BitVec.length op2_in) == 16) || (((Sail.BitVec.length op2_in) == 32) || ((Sail.BitVec.length op2_in) == 64))) "src/v8_base.sail:16782.41-16782.42"
  let op1 : (BitVec k_N) := op1_in
  let op2 : (BitVec k_N) := op2_in
  let type1 ← (( do
    let (__tup_0, _, _) ← do (FPUnpack op1 fpcr)
    (pure __tup_0) ) : SailM FPType )
  let type2 ← (( do
    let (__tup_0, _, _) ← do (FPUnpack op2 fpcr)
    (pure __tup_0) ) : SailM FPType )
  let type1_nan : Bool := ((BEq.beq type1 FPType_QNaN) || (BEq.beq type1 FPType_SNaN))
  let type2_nan : Bool := ((BEq.beq type2 FPType_QNaN) || (BEq.beq type2 FPType_SNaN))
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let (op1, op2) ← (( do
    if ((! ((altfp && type1_nan) && type2_nan)) : Bool)
    then
      (do
        let (op1, op2) ← (( do
          if (((BEq.beq type1 FPType_QNaN) && (bne type2 FPType_QNaN)) : Bool)
          then
            (do
              let op1 ← (FPInfinity 0#1 (Sail.BitVec.length op2_in))
              (pure (op1, op2)))
          else
            (do
              let op2 ← (( do
                if (((bne type1 FPType_QNaN) && (BEq.beq type2 FPType_QNaN)) : Bool)
                then (do (FPInfinity 0#1 (Sail.BitVec.length op2_in)))
                else (pure op2) ) : SailM (BitVec k_N) )
              (pure (op1, op2))) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
        (pure (op1, op2)))
    else (pure (op1, op2)) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
  let altfmaxfmin : Bool := false
  (FPMin__1 op1 op2 fpcr altfmaxfmin)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMul (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length result) == 64))) "src/v8_base.sail:16824.41-16824.42"
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs type1 type2 op1 op2 fpcr)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let result ← (( do
        if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
        then
          (do
            let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
            (FPProcessException FPExc_InvalidOp fpcr)
            (pure result))
        else
          (do
            if ((inf1 || inf2) : Bool)
            then (do (FPInfinity (sign1 ^^^ sign2) (Sail.BitVec.length result)))
            else
              (do
                if ((zero1 || zero2) : Bool)
                then (do (FPZero (sign1 ^^^ sign2) (Sail.BitVec.length result)))
                else (do (FPRound (mult_real value1_name value2_name) fpcr (Sail.BitVec.length result))))) ) : SailM (BitVec k_N) )
      (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
      (pure result))
  else (pure result)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMulAdd (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (FPMulAdd__1 addend op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMulAdd_ZA (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := false
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  (FPMulAdd__1 addend op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMulX (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:17040.41-17040.42"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs type1 type2 op1 op2 fpcr)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let result ← (( do
        if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
        then (do (FPTwo (sign1 ^^^ sign2) (Sail.BitVec.length result)))
        else
          (do
            if ((inf1 || inf2) : Bool)
            then (do (FPInfinity (sign1 ^^^ sign2) (Sail.BitVec.length result)))
            else
              (do
                if ((zero1 || zero2) : Bool)
                then (do (FPZero (sign1 ^^^ sign2) (Sail.BitVec.length result)))
                else (do (FPRound (mult_real value1_name value2_name) fpcr (Sail.BitVec.length result))))) ) : SailM (BitVec k_N) )
      (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
      (pure result))
  else (pure result)

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPMulAddH (addend : (BitVec k_N)) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (FPMulAddH__1 addend op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPMulAddH_ZA (addend : (BitVec k_N)) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := false
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  (FPMulAddH__1 addend op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPSqrt (op : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:17724.41-17724.42"
  let (fptype, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op fpcr)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op)) ) : SailM (BitVec k_N) )
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then (do (FPProcessNaN fptype op fpcr))
  else
    (do
      if ((BEq.beq fptype FPType_Zero) : Bool)
      then (do (FPZero sign (Sail.BitVec.length result)))
      else
        (do
          if (((BEq.beq fptype FPType_Infinity) && (sign == 0#1)) : Bool)
          then (do (FPInfinity sign (Sail.BitVec.length result)))
          else
            (do
              if ((sign == 1#1) : Bool)
              then
                (do
                  let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
                  (FPProcessException FPExc_InvalidOp fpcr)
                  (pure result))
              else
                (do
                  let result ← (FPRound (sqrt_real value_name) fpcr (Sail.BitVec.length result))
                  (FPProcessDenorm fptype (Sail.BitVec.length result) fpcr)
                  (pure result)))))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPSub (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (FPSub__1 op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPSub_ZA (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := false
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  (FPSub__1 op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPRecipStepFused (op1_in : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:29114.41-29114.42"
  let op1 : (BitVec k_N) := op1_in
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let op1 ← (( do (FPNeg op1) ) : SailM (BitVec k_N) )
  let altfp ← (( do (pure ((← (HaveAltFP ())) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then (Sail.BitVec.updateSubrange fpcr 23 22 0b00#2)
    else fpcr
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1 fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2 fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs__1 type1 type2 op1 op2 fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
      then (do (FPTwo 0#1 (Sail.BitVec.length result)))
      else
        (do
          if ((inf1 || inf2) : Bool)
          then (do (FPInfinity (sign1 ^^^ sign2) (Sail.BitVec.length result)))
          else
            (do
              let result_value : real := (add_real (2) (mult_real value1_name value2_name))
              if ((eq_real result_value (0)) : Bool)
              then
                (do
                  let sign : (BitVec 1) :=
                    if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                    then 1#1
                    else 0#1
                  (FPZero sign (Sail.BitVec.length result)))
              else (do (FPRound__2 result_value fpcr rounding fpexc (Sail.BitVec.length result))))))
  else (pure result)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPRSqrtStepFused (op1_in : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:29172.41-29172.42"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let op1 : (BitVec k_N) := op1_in
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let op1 ← (( do (FPNeg op1) ) : SailM (BitVec k_N) )
  let altfp ← (( do (pure ((← (HaveAltFP ())) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then (Sail.BitVec.updateSubrange fpcr 23 22 0b00#2)
    else fpcr
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op1 fpcr fpexc)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 op2 fpcr fpexc)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs__1 type1 type2 op1 op2 fpcr fpexc)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
      then (do (FPOnePointFive 0#1 (Sail.BitVec.length result)))
      else
        (do
          if ((inf1 || inf2) : Bool)
          then (do (FPInfinity (sign1 ^^^ sign2) (Sail.BitVec.length result)))
          else
            (do
              let result_value : real := (div_real (add_real (3) (mult_real value1_name value2_name)) (2))
              if ((eq_real result_value (0)) : Bool)
              then
                (do
                  let sign : (BitVec 1) :=
                    if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                    then 1#1
                    else 0#1
                  (FPZero sign (Sail.BitVec.length result)))
              else (do (FPRound__2 result_value fpcr rounding fpexc (Sail.BitVec.length result))))))
  else (pure result)

/-- Type quantifiers: k_N : Nat, scale : Int, List.elem k_N [16, 32, 64] -/
def FPScale (op : (BitVec k_N)) (scale : Int) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:29967.41-29967.42"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op)) ) : SailM (BitVec k_N) )
  let (fptype, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op fpcr)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fptype, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then (do (FPProcessNaN fptype op fpcr))
  else
    (do
      if ((BEq.beq fptype FPType_Zero) : Bool)
      then (do (FPZero sign (Sail.BitVec.length result)))
      else
        (do
          if ((BEq.beq fptype FPType_Infinity) : Bool)
          then (do (FPInfinity sign (Sail.BitVec.length result)))
          else
            (do
              let scale_opt := (GetOptimizedScale op scale (Sail.BitVec.length result))
              let result ← (FPRound (mult_real value_name (real_power (2) scale_opt)) fpcr (Sail.BitVec.length result))
              (FPProcessDenorm fptype (Sail.BitVec.length result) fpcr)
              (pure result))))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPTrigSSel (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:30017.41-30017.42"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  if (((BitVec.join1 [(BitVec.access op2 0)]) == 1#1) : Bool)
  then (do (FPOne (BitVec.join1 [(BitVec.access op2 1)]) (Sail.BitVec.length result)))
  else
    (do
      if (((BitVec.join1 [(BitVec.access op2 1)]) == 1#1) : Bool)
      then (do (FPNeg op1))
      else (pure op1))

/-- Type quantifiers: M : Nat, k_N : Nat, List.elem M [16, 32, 64] ∧ List.elem k_N [16, 32, 64] -/
def FPConvertSVE (op : (BitVec k_N)) (fpcr_in : (BitVec 64)) (rounding : FPRounding) (M : Nat) : SailM (BitVec M) := do
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  (FPConvert op fpcr rounding M)

/-- Type quantifiers: M : Nat, k_N : Nat, List.elem M [16, 32, 64] ∧ List.elem k_N [16, 32, 64] -/
def FPConvertSVE__1 (op : (BitVec k_N)) (fpcr_in : (BitVec 64)) (M : Nat) : SailM (BitVec M) := do
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  (FPConvert op fpcr (← (FPRoundingMode fpcr)) M)

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def BFMulAddH (addend : (BitVec k_N)) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  sail_assert ((Sail.BitVec.length addend) == 32) "src/v8_base.sail:32181.19-32181.20"
  let value1_name : (BitVec k_N) := (op1 +++ (Zeros (n := (Int.ediv (Sail.BitVec.length addend) 2))))
  let value2_name : (BitVec k_N) := (op2 +++ (Zeros (n := (Int.ediv (Sail.BitVec.length value1_name) 2))))
  let fpcr : FPCRType := fpcr_in
  let altfp ← (( do (pure ((← (HaveAltFP ())) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then (Sail.BitVec.updateSubrange fpcr 23 22 0b00#2)
    else fpcr
  (FPMulAdd__1 addend value1_name value2_name fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPConvertBF__1 (op : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec (k_N / 2)) := do
  (FPConvertBF op fpcr (← (FPRoundingMode fpcr)))

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def BFDotAdd (addend : (BitVec k_N)) (op1_a : (BitVec (k_N / 2))) (op1_b : (BitVec (k_N / 2))) (op2_a : (BitVec (k_N / 2))) (op2_b : (BitVec (k_N / 2))) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  sail_assert ((Sail.BitVec.length addend) == 32) "src/v8_base.sail:32396.19-32396.20"
  let fpcr : FPCRType := fpcr_in
  let prod ← (( do (undefined_bitvector (Sail.BitVec.length addend)) ) : SailM (BitVec k_N) )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length prod)) ) : SailM (BitVec k_N) )
  if (((! (← (HaveEBF16 ()))) || ((_get_FPCRType_EBF fpcr) == 0#1)) : Bool)
  then
    (do
      let prod ← (( do (FPAdd_BF16 (← (BFMulH op1_a op2_a)) (← (BFMulH op1_b op2_b))) ) : SailM (BitVec k_N) )
      (FPAdd_BF16 addend prod))
  else
    (do
      let isbfloat16 : Bool := true
      let fpexc : Bool := false
      let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
      let prod ← (( do (FPDot__1 op1_a op1_b op2_a op2_b fpcr isbfloat16 fpexc) ) : SailM (BitVec k_N) )
      (FPAdd__1 addend prod fpcr fpexc))

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFAdd (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (BFAdd__1 op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFAdd_ZA (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := false
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  (BFAdd__1 op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFSub (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (BFSub__1 op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFSub_ZA (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := false
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  (BFSub__1 op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMulAdd (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (BFMulAdd__1 addend op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMulAdd_ZA (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := false
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  (BFMulAdd__1 addend op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMul (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (BFMul__1 op1 op2 fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMin (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  (BFMin__1 op1 op2 fpcr altfp)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMinNum (op1_in : (BitVec k_N)) (op2_in : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  sail_assert ((Sail.BitVec.length op2_in) == 16) "src/v8_base.sail:32871.19-32871.20"
  let fpexc : Bool := true
  let isbfloat16 : Bool := true
  let op1 : (BitVec k_N) := op1_in
  let op2 : (BitVec k_N) := op2_in
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let type1 ← (( do
    let (__tup_0, _, _) ← do (FPUnpackBase__1 op1 fpcr fpexc isbfloat16)
    (pure __tup_0) ) : SailM FPType )
  let type2 ← (( do
    let (__tup_0, _, _) ← do (FPUnpackBase__1 op2 fpcr fpexc isbfloat16)
    (pure __tup_0) ) : SailM FPType )
  let type1_nan : Bool := ((BEq.beq type1 FPType_QNaN) || (BEq.beq type1 FPType_SNaN))
  let type2_nan : Bool := ((BEq.beq type2 FPType_QNaN) || (BEq.beq type2 FPType_SNaN))
  let (op1, op2) ← (( do
    if ((! ((altfp && type1_nan) && type2_nan)) : Bool)
    then
      (do
        let (op1, op2) ← (( do
          if (((BEq.beq type1 FPType_QNaN) && (bne type2 FPType_QNaN)) : Bool)
          then
            (do
              let op1 ← (BFInfinity 0#1 (Sail.BitVec.length op2_in))
              (pure (op1, op2)))
          else
            (do
              let op2 ← (( do
                if (((bne type1 FPType_QNaN) && (BEq.beq type2 FPType_QNaN)) : Bool)
                then (do (BFInfinity 0#1 (Sail.BitVec.length op2_in)))
                else (pure op2) ) : SailM (BitVec k_N) )
              (pure (op1, op2))) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
        (pure (op1, op2)))
    else (pure (op1, op2)) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
  let altfmaxfmin : Bool := false
  (BFMin__1 op1 op2 fpcr altfmaxfmin)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMax (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  (BFMax__1 op1 op2 fpcr altfp)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMaxNum (op1_in : (BitVec k_N)) (op2_in : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  sail_assert ((Sail.BitVec.length op2_in) == 16) "src/v8_base.sail:32968.19-32968.20"
  let fpexc : Bool := true
  let isbfloat16 : Bool := true
  let op1 : (BitVec k_N) := op1_in
  let op2 : (BitVec k_N) := op2_in
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let type1 ← (( do
    let (__tup_0, _, _) ← do (FPUnpackBase__1 op1 fpcr fpexc isbfloat16)
    (pure __tup_0) ) : SailM FPType )
  let type2 ← (( do
    let (__tup_0, _, _) ← do (FPUnpackBase__1 op2 fpcr fpexc isbfloat16)
    (pure __tup_0) ) : SailM FPType )
  let type1_nan : Bool := ((BEq.beq type1 FPType_QNaN) || (BEq.beq type1 FPType_SNaN))
  let type2_nan : Bool := ((BEq.beq type2 FPType_QNaN) || (BEq.beq type2 FPType_SNaN))
  let (op1, op2) ← (( do
    if ((! ((altfp && type1_nan) && type2_nan)) : Bool)
    then
      (do
        let (op1, op2) ← (( do
          if (((BEq.beq type1 FPType_QNaN) && (bne type2 FPType_QNaN)) : Bool)
          then
            (do
              let op1 ← (BFInfinity 1#1 (Sail.BitVec.length op2_in))
              (pure (op1, op2)))
          else
            (do
              let op2 ← (( do
                if (((bne type1 FPType_QNaN) && (BEq.beq type2 FPType_QNaN)) : Bool)
                then (do (BFInfinity 1#1 (Sail.BitVec.length op2_in)))
                else (pure op2) ) : SailM (BitVec k_N) )
              (pure (op1, op2))) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
        (pure (op1, op2)))
    else (pure (op1, op2)) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
  let altfmaxfmin : Bool := false
  (BFMax__1 op1 op2 fpcr altfmaxfmin)

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPDotAdd (addend : (BitVec k_N)) (op1_a : (BitVec (k_N / 2))) (op1_b : (BitVec (k_N / 2))) (op2_a : (BitVec (k_N / 2))) (op2_b : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  sail_assert ((Sail.BitVec.length addend) == 32) "src/v8_base.sail:33025.19-33025.20"
  let isbfloat16 : Bool := false
  let fpexc : Bool := true
  let prod ← (( do (FPDot__1 op1_a op1_b op2_a op2_b fpcr isbfloat16 fpexc) ) : SailM (BitVec k_N) )
  (FPAdd__1 addend prod fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPDotAdd_ZA (addend : (BitVec k_N)) (op1_a : (BitVec (k_N / 2))) (op1_b : (BitVec (k_N / 2))) (op2_a : (BitVec (k_N / 2))) (op2_b : (BitVec (k_N / 2))) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpcr : FPCRType := fpcr_in
  sail_assert ((Sail.BitVec.length addend) == 32) "src/v8_base.sail:33038.19-33038.20"
  let isbfloat16 : Bool := false
  let fpexc : Bool := false
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  let prod ← (( do (FPDot__1 op1_a op1_b op2_a op2_b fpcr isbfloat16 fpexc) ) : SailM (BitVec k_N) )
  (FPAdd__1 addend prod fpcr fpexc)

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV88 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap8_IMPLEMENTED enabled
  if (enabled : Bool)
  then (__ConfigureV87 enabled)
  else (pure ())

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV92 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap2_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV91 enabled)
      (__ConfigureV87 enabled))
  else (pure ())

def CheckAdvSIMDEnabled (_ : Unit) : SailM Unit := do
  let fpexc_check : Bool := true
  let advsimd : Bool := true
  (AArch32_CheckAdvSIMDOrFPEnabled fpexc_check advsimd)
  let loop_i_lower := 0
  let loop_i_upper := 31
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do writeReg _Dclone (vectorUpdate (← readReg _Dclone) i (← (D_read i)))
  (pure loop_vars)

/-- Type quantifiers: k_advsimd : Bool, k_include_fpexc_check_name : Bool -/
def CheckAdvSIMDOrVFPEnabled (include_fpexc_check_name : Bool) (advsimd : Bool) : SailM Unit := do
  (AArch32_CheckAdvSIMDOrFPEnabled include_fpexc_check_name advsimd)

/-- Type quantifiers: k_include_fpexc_check_name : Bool -/
def CheckVFPEnabled (include_fpexc_check_name : Bool) : SailM Unit := do
  let advsimd : Bool := false
  (AArch32_CheckAdvSIMDOrFPEnabled include_fpexc_check_name advsimd)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPHalvedSub (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let result_sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length result) == 64))) "src/v8_base.sail:41774.41-41774.42"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs type1 type2 op1 op2 fpcr)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      if (((inf1 && inf2) && (sign1 == sign2)) : Bool)
      then
        (do
          let result ← (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))
          (FPProcessException FPExc_InvalidOp fpcr)
          (pure result))
      else
        (do
          if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 1#1))) : Bool)
          then (do (FPInfinity 0#1 (Sail.BitVec.length result)))
          else
            (do
              if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 0#1))) : Bool)
              then (do (FPInfinity 1#1 (Sail.BitVec.length result)))
              else
                (do
                  if (((zero1 && zero2) && (sign1 != sign2)) : Bool)
                  then (do (FPZero sign1 (Sail.BitVec.length result)))
                  else
                    (do
                      let result_value : real := (div_real (sub_real value1_name value2_name) (2))
                      if ((eq_real result_value (0)) : Bool)
                      then
                        (do
                          let result_sign : (BitVec 1) :=
                            if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                            then 1#1
                            else 0#1
                          (FPZero result_sign (Sail.BitVec.length result)))
                      else (do (FPRound result_value fpcr (Sail.BitVec.length result))))))))
  else (pure result)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPTrigSMul (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:30004.41-30004.42"
  let result ← (( do (FPMul op1 op1 fpcr) ) : SailM (BitVec k_N) )
  let fpexc : Bool := false
  let fptype ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack__1 result fpcr fpexc)
    let fptype : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure fptype) ) : SailM FPType )
  if ((! ((BEq.beq fptype FPType_QNaN) || (BEq.beq fptype FPType_SNaN))) : Bool)
  then (pure (BitVec.update result ((Sail.BitVec.length result) -i 1) (Bit (BitVec.join1 [(BitVec.access op2 0)]))))
  else (pure result)

/-- Type quantifiers: k_N : Nat, x_in : Int, List.elem k_N [16, 32, 64] -/
def FPTrigMAdd (x_in : Int) (op1 : (BitVec k_N)) (op2_in : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  sail_assert (((Sail.BitVec.length op2_in) == 16) || (((Sail.BitVec.length op2_in) == 32) || ((Sail.BitVec.length op2_in) == 64))) "src/v8_base.sail:30202.41-30202.42"
  let op2 : (BitVec k_N) := op2_in
  let x : Int := x_in
  sail_assert (x ≥b 0) "src/v8_base.sail:30205.17-30205.18"
  sail_assert (x <b 8) "src/v8_base.sail:30206.16-30206.17"
  let x : Int :=
    if (((BitVec.join1 [(BitVec.access op2 ((Sail.BitVec.length op2_in) -i 1))]) == 1#1) : Bool)
    then (x +i 8)
    else x
  let x := x
  let coeff ← (( do (FPTrigMAddCoefficient_read x (Sail.BitVec.length op2_in)) ) : SailM (BitVec k_N) )
  let op2 ← (( do (FPAbs op2) ) : SailM (BitVec k_N) )
  (FPMulAdd coeff op1 op2 fpcr)

/-- Type quantifiers: k_ex8453729_ : Bool, k_N : Nat, esize : Nat, List.elem k_N [8, 16, 32, 64, 128, 256, 512, 1024, 2048] ∧ List.elem esize [8, 16, 32, 64] ∧ k_N ≥ esize -/
partial def Reduce__1 (op : ReduceOp) (input : (BitVec k_N)) (esize : Nat) (altfp : Bool) : SailM (BitVec esize) := do
  sail_assert ((esize == 8) || ((esize == 16) || ((esize == 32) || (esize == 64)))) "src/v8_base.sail:30829.63-30829.64"
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  if (((Sail.BitVec.length input) == esize) : Bool)
  then (pure (Sail.BitVec.extractLsb input (esize -i 1) 0))
  else
    (do
      let half := (Int.ediv (Sail.BitVec.length input) 2)
      let hi ← (( do (Reduce__1 op (Sail.BitVec.extractLsb input ((Sail.BitVec.length input) -i 1) half) esize altfp) ) : SailM (BitVec esize) )
      let lo ← (( do (Reduce__1 op (Sail.BitVec.extractLsb input (half -i 1) 0) esize altfp) ) : SailM (BitVec esize) )
      match op with
      | .ReduceOp_FMINNUM =>
        (do
          sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/v8_base.sail:30839.51-30839.52"
          (FPMinNum lo hi (← (FPCR_read ()))))
      | .ReduceOp_FMAXNUM =>
        (do
          sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/v8_base.sail:30843.51-30843.52"
          (FPMaxNum lo hi (← (FPCR_read ()))))
      | .ReduceOp_FMIN =>
        (do
          sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/v8_base.sail:30847.51-30847.52"
          (FPMin__1 lo hi (← (FPCR_read ())) altfp))
      | .ReduceOp_FMAX =>
        (do
          sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/v8_base.sail:30851.51-30851.52"
          (FPMax__1 lo hi (← (FPCR_read ())) altfp))
      | .ReduceOp_FADD =>
        (do
          sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/v8_base.sail:30855.51-30855.52"
          (FPAdd lo hi (← (FPCR_read ()))))
      | .ReduceOp_ADD => (pure (lo + hi)))
termination_by (let (op, input, esize, altfp) := (op, input, esize, altfp)
(Sail.BitVec.length input)).toNat

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def BFMulAddH_ZA (addend : (BitVec k_N)) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  sail_assert ((Sail.BitVec.length addend) == 32) "src/v8_base.sail:32200.19-32200.20"
  let value1_name : (BitVec k_N) := (op1 +++ (Zeros (n := (Int.ediv (Sail.BitVec.length addend) 2))))
  let value2_name : (BitVec k_N) := (op2 +++ (Zeros (n := (Int.ediv (Sail.BitVec.length value1_name) 2))))
  (FPMulAdd_ZA addend value1_name value2_name fpcr)

/-- Type quantifiers: k_N : Nat, k_N = 128 -/
def BFMatMulAdd (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  sail_assert ((Sail.BitVec.length op2) == 128) "src/v8_base.sail:32417.20-32417.21"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let sum ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (result, sum) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 1
    let mut loop_vars := (result, sum)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (result, sum) := loop_vars
      loop_vars ← do
        let (result, sum) ← (( do
          let loop_j_lower := 0
          let loop_j_upper := 1
          let mut loop_vars_1 := (result, sum)
          for j in [loop_j_lower:loop_j_upper:1]i do
            let (result, sum) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (Elem_read addend ((2 *i i) +i j) 32)
              let sum ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 1
                let mut loop_vars_2 := sum
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let elt1_a ← (( do (Elem_read op1 (((4 *i i) +i (2 *i k)) +i 0) 16) ) : SailM (BitVec 16) )
                    let elt1_b ← (( do (Elem_read op1 (((4 *i i) +i (2 *i k)) +i 1) 16) ) : SailM (BitVec 16) )
                    let elt2_a ← (( do (Elem_read op2 (((4 *i j) +i (2 *i k)) +i 0) 16) ) : SailM (BitVec 16) )
                    let elt2_b ← (( do (Elem_read op2 (((4 *i j) +i (2 *i k)) +i 1) 16) ) : SailM (BitVec 16) )
                    (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ())))
                (pure loop_vars_2) ) : SailM (BitVec 32) )
              let result ← (Elem_set result ((2 *i i) +i j) 32 sum)
              (pure (result, sum))
          (pure loop_vars_1) ) : SailM ((BitVec k_N) × (BitVec 32)) )
        (pure (result, sum))
    (pure loop_vars) ) : SailM ((BitVec k_N) × (BitVec 32)) )
  (pure result)

/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 ∧ esize = 16 ∨ esize = 32 ∨ esize = 64 ∨ (not (k_N = (esize * 2 * 2))) -/
def FPMatMulAdd (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (esize : Int) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  sail_assert ((Sail.BitVec.length op2) == ((esize *i 2) *i 2)) "src/v8_base.sail:33003.30-33003.31"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let prod0 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let prod1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let sum ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (prod0, prod1, result, sum) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 1
    let mut loop_vars := (prod0, prod1, result, sum)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (prod0, prod1, result, sum) := loop_vars
      loop_vars ← do
        let (prod0, prod1, result, sum) ← (( do
          let loop_j_lower := 0
          let loop_j_upper := 1
          let mut loop_vars_1 := (prod0, prod1, result, sum)
          for j in [loop_j_lower:loop_j_upper:1]i do
            let (prod0, prod1, result, sum) := loop_vars_1
            loop_vars_1 ← do
              sail_assert (((((2 *i i) +i j) *i esize) ≤b (((((2 *i i) +i j) *i esize) +i esize) -i 1)) || ((! ((((2 *i i) +i j) ≥b 0) && (((((2 *i i) +i j) +i 1) *i esize) ≤b (Sail.BitVec.length result)))) || (! ((Sail.BitVec.length result) == ((esize *i 2) *i 2))))) "src/v8_base.sail:33010.223-33010.224"
              let sum ← (Elem_read addend ((2 *i i) +i j) esize)
              let prod0 ← (FPMul (← (Elem_read op1 ((2 *i i) +i 0) esize)) (← (Elem_read op2 ((2 *i j) +i 0) esize)) fpcr)
              let prod1 ← (FPMul (← (Elem_read op1 ((2 *i i) +i 1) esize)) (← (Elem_read op2 ((2 *i j) +i 1) esize)) fpcr)
              let sum ← (FPAdd sum (← (FPAdd prod0 prod1 fpcr)) fpcr)
              let result ← (Elem_set result ((2 *i i) +i j) esize sum)
              (pure (prod0, prod1, result, sum))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec k_N) × (BitVec esize)) )
        (pure (prod0, prod1, result, sum))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec k_N) × (BitVec esize)) )
  (pure result)

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV89 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap9_IMPLEMENTED enabled
  if (enabled : Bool)
  then (__ConfigureV88 enabled)
  else (pure ())

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV93 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap3_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV92 enabled)
      (__ConfigureV88 enabled))
  else (pure ())

def CheckCryptoEnabled32 (_ : Unit) : SailM Unit := do
  (CheckAdvSIMDEnabled ())

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32] -/
def FPRecipStep (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length result) == 16) || ((Sail.BitVec.length result) == 32)) "src/v8_base.sail:41831.30-41831.31"
  let fpcr ← (( do (StandardFPSCRValue ()) ) : SailM FPCRType )
  let type1 ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure type1) ) : SailM FPType )
  let type2 ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure type2) ) : SailM FPType )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs type1 type2 op1 op2 fpcr)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let product ← (( do (undefined_bitvector (Sail.BitVec.length result)) ) : SailM (BitVec k_N) )
      let product ← (( do
        if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
        then (do (FPZero 0#1 (Sail.BitVec.length result)))
        else (do (FPMul op1 op2 fpcr)) ) : SailM (BitVec k_N) )
      let two ← (( do (FPTwo 0#1 (Sail.BitVec.length result)) ) : SailM (BitVec k_N) )
      (FPSub two product fpcr))
  else (pure result)

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32] -/
def FPRSqrtStep (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert (((Sail.BitVec.length result) == 16) || ((Sail.BitVec.length result) == 32)) "src/v8_base.sail:41868.30-41868.31"
  let fpcr ← (( do (StandardFPSCRValue ()) ) : SailM FPCRType )
  let type1 ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op1 fpcr)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure type1) ) : SailM FPType )
  let type2 ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpack op2 fpcr)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure type2) ) : SailM FPType )
  let (done, result) ← (( do
    let (tup__0, tup__1) ← do (FPProcessNaNs type1 type2 op1 op2 fpcr)
    let done : Bool := tup__0
    let result : (BitVec k_N) := tup__1
    (pure (done, result)) ) : SailM (Bool × (BitVec k_N)) )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let product ← (( do (undefined_bitvector (Sail.BitVec.length result)) ) : SailM (BitVec k_N) )
      let product ← (( do
        if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
        then (do (FPZero 0#1 (Sail.BitVec.length result)))
        else (do (FPMul op1 op2 fpcr)) ) : SailM (BitVec k_N) )
      let three ← (( do (FPThree 0#1 (Sail.BitVec.length result)) ) : SailM (BitVec k_N) )
      (FPHalvedSub three product fpcr))
  else (pure result)

/-- Type quantifiers: k_N : Nat, esize : Nat, List.elem k_N [8, 16, 32, 64, 128, 256, 512, 1024, 2048] ∧ List.elem esize [8, 16, 32, 64] ∧ k_N ≥ esize -/
def Reduce (op : ReduceOp) (input : (BitVec k_N)) (esize : Nat) : SailM (BitVec esize) := do
  let altfp ← (( do (HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))) <&&> (do (pure ((_get_FPCR_Type_AH (← readReg FPCR)) == 1#1))) ) : SailM Bool )
  (Reduce__1 op input esize altfp)

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV94 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap4_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV93 enabled)
      (__ConfigureV89 enabled))
  else (pure ())

/-- Type quantifiers: k_M : Nat, k_N : Nat, k_esize : Nat, k_N ≥ 0 ∧ k_M ≥ 0 ∧ k_esize ≥ 0 -/
def ReducePredicated (op : ReduceOp) (input : (BitVec k_N)) (mask : (BitVec k_M)) (identity : (BitVec k_esize)) : SailM (BitVec k_esize) := do
  sail_assert ((Sail.BitVec.length input) == ((Sail.BitVec.length mask) *i 8)) "src/v8_base.sail:30871.23-30871.24"
  let p2bits ← do (CeilPow2 (Sail.BitVec.length input))
  let operand ← (( do (undefined_bitvector p2bits) ) : SailM (BitVec p2bits) )
  let elements := (fdiv_int p2bits (Sail.BitVec.length identity))
  let operand ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := operand
    for e in [loop_e_lower:loop_e_upper:1]i do
      let operand := loop_vars
      loop_vars ← do
        if ((←((pure ((e *i (Sail.BitVec.length identity)) <b (Sail.BitVec.length input))) <&&> (do
             (ActivePredicateElement mask e (Sail.BitVec.length identity))))) : Bool)
        then
          (do
            sail_assert ((Sail.BitVec.length input) ≥b 0) "src/v8_base.sail:30877.38-30877.39"
            sail_assert ((Sail.BitVec.length identity) ≥b 0) "src/v8_base.sail:30878.42-30878.43"
            sail_assert (((e *i (Sail.BitVec.length identity)) ≤b (((e *i (Sail.BitVec.length identity)) +i (Sail.BitVec.length identity)) -i 1)) || (! ((e ≥b 0) && (((e +i 1) *i (Sail.BitVec.length identity)) ≤b (Sail.BitVec.length input))))) "src/v8_base.sail:30879.135-30879.136"
            (Elem_set operand e (Sail.BitVec.length identity) (← (Elem_read input e (Sail.BitVec.length identity)))))
        else
          (do
            sail_assert (p2bits ≥b 0) "src/v8_base.sail:30882.43-30882.44"
            sail_assert ((Sail.BitVec.length identity) ≥b 0) "src/v8_base.sail:30883.42-30883.43"
            sail_assert (((e *i (Sail.BitVec.length identity)) ≤b (((e +i 1) *i (Sail.BitVec.length identity)) -i 1)) || (! ((e ≥b 0) && (((e +i 1) *i (Sail.BitVec.length identity)) ≤b p2bits)))) "src/v8_base.sail:30884.137-30884.138"
            (Elem_set operand e (Sail.BitVec.length identity) identity))
    (pure loop_vars) ) : SailM (BitVec p2bits) )
  sail_assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && ((((((Sail.BitVec.length identity) == 8) || ((Sail.BitVec.length identity) == 16)) || ((Sail.BitVec.length identity) == 32)) || ((Sail.BitVec.length identity) == 64)) && (p2bits ≥b (Sail.BitVec.length identity)))) || (! ((Sail.BitVec.length input) == ((Sail.BitVec.length mask) *i 8)))) "src/v8_base.sail:30888.143-30888.144"
  (Reduce op operand (Sail.BitVec.length identity))


