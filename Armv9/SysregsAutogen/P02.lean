import Armv9.Flow
import Armv9.Prelude
import Armv9.V8Base
import Armv9.Stubs

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

/-- Type quantifiers: t : Int -/
def DBGVCR32_EL2_SysRegRead_6fe9bc763220955c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (HaveAArch32EL EL1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_DBGVCR32_EL2 (← readReg DBGVCR32_EL2)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_DBGVCR32_EL2 (← readReg DBGVCR32_EL2)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_0d4001a88a9206f8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (13 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((13 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 13)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 13)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 13)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_236e531d61e35213 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (15 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((15 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 15)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 15)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 15)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_2c1cc2102bf556aa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (8 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((8 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 8)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 8)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 8)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_6ed96d96594172dd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (11 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((11 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 11)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 11)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 11)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_732a44d59c35aeb3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (9 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((9 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 9)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 9)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 9)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_74bf5d2a6cfe195c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (6 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((6 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 6)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 6)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 6)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_782b8628944ba11a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (1 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((1 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 1)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 1)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 1)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_7e97fa1e73481f2d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (7 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((7 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 7)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 7)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 7)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_81a0b83ef7c202d4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (5 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((5 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 5)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 5)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 5)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_9b436b8dcf826854 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (14 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((14 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 14)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 14)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 14)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_a0df5130cffc6ec3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (2 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((2 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 2)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 2)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 2)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_aae6422db875ace5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (0 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((0 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 0)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 0)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_ab00b8f6b1bf63cc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (4 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((4 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 4)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 4)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 4)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_b7d3a0a1687ee605 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (12 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((12 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 12)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 12)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 12)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_d41ce14d142d5fc9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (3 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((3 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 3)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 3)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 3)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegRead_d6acb1282794050a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (10 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((10 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 10)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 10)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWCR_EL1 (GetElem?.getElem! (← readReg DBGWCR_EL1) 10)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_06f47f0db897fdec (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (2 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((2 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 2)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 2)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 2)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_19cc269e021d29f0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (0 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((0 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 0)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 0)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_27540f902a0177f1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (14 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((14 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 14)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 14)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 14)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_395e92ea6cb1cbd3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (9 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((9 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 9)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 9)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 9)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_3ad260c7658f264f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (12 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((12 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 12)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 12)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 12)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_3ea4dd4eabbc6db1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (13 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((13 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 13)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 13)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 13)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_419765ae001a7669 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (15 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((15 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 15)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 15)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 15)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_469f2550ef085d68 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (6 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((6 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 6)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 6)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 6)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_5cfc3b8e8ae8a2a4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (5 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((5 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 5)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 5)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 5)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_695a90ac9c89a050 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (1 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((1 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 1)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 1)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 1)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_6c69a5a56e08fe81 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (11 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((11 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 11)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 11)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 11)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_9cebffd3d1c8ceeb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (3 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((3 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 3)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 3)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 3)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_bfffa222b59a2eac (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (10 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((10 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 10)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 10)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 10)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_dd3a55e2d9bbec8f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (4 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((4 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 4)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 4)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 4)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_e481fcd4bbdbbbdd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (8 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((8 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 8)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 8)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 8)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_fae261a7c3341309 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (7 ≥b (← readReg NUM_WATCHPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((7 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) *i 16)) ≥b (← readReg NUM_WATCHPOINTS))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 7)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 7)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! (← readReg DBGWVR_EL1) 7)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DCZID_EL0_SysRegRead_9bb2971f34b1558f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_DCZID_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_DCZID_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_DCZID_EL0 == 1#1)) : Bool)
      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
      else (X_set t 64 (__get_DCZID_EL0 (← readReg DCZID_EL0))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_DCZID_EL0 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_DCZID_EL0 (← readReg DCZID_EL0))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_DCZID_EL0 (← readReg DCZID_EL0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_DCZID_EL0 (← readReg DCZID_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DIT_SysRegRead_80b5d608e76aa495 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (X_set t 64 (((Zeros (n := 39)) +++ (← readReg PSTATE).DIT) +++ (Zeros (n := 24))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (((Zeros (n := 39)) +++ (← readReg PSTATE).DIT) +++ (Zeros (n := 24))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (((Zeros (n := 39)) +++ (← readReg PSTATE).DIT) +++ (Zeros (n := 24))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (((Zeros (n := 39)) +++ (← readReg PSTATE).DIT) +++ (Zeros (n := 24))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DLR_EL0_SysRegRead_635696e4f590448d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (X_set t 64 (← readReg DLR_EL0))

/-- Type quantifiers: t : Int -/
def DSPSR_EL0_SysRegRead_e92e924519c42368 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (X_set t 64 (__get_DSPSR_EL0 (← readReg DSPSR_EL0)))

/-- Type quantifiers: t : Int -/
def ELR_EL1_SysRegRead_a79af82b86a9e639 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x230#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (← readReg ELR_EL1))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg ELR_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ELR_EL2_SysRegRead_98b7799847de6b3f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← readReg ELR_EL1))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ELR_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ELR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ELR_EL2_SysRegRead_cdeb265f6e920d74 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b011#3))))) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x230#12))))
              else (X_set t 64 (← readReg ELR_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (← readReg ELR_EL2))
              else (X_set t 64 (← readReg ELR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ELR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ELR_EL3_SysRegRead_48156757f03c05da (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ELR_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERRIDR_EL1_SysRegRead_1405fcd9adc2c3a9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERRIDR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERRIDR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERRIDR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ERRIDR_EL1 (← readReg ERRIDR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_ERRIDR_EL1 (← readReg ERRIDR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ERRIDR_EL1 (← readReg ERRIDR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERRSELR_EL1_SysRegRead_8615029c42903774 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERRSELR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERRSELR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERRSELR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ERRSELR_EL1 (← readReg ERRSELR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_ERRSELR_EL1 (← readReg ERRSELR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ERRSELR_EL1 (← readReg ERRSELR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXADDR_EL1_SysRegRead_e08903d0b9a89a31 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXADDR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXADDR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXADDR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXADDR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXADDR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXADDR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXCTLR_EL1_SysRegRead_e46adf59deec13d6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXCTLR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXCTLR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXCTLR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXCTLR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXCTLR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXCTLR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXFR_EL1_SysRegRead_f8186cd7f820b3af (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXFR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXFR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXFR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXFR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXFR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXFR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXGSR_EL1_SysRegRead_63b383efe8ec0d4f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR2_EL2_nERXGSR_EL1 ← (( do (pure (_get_HFGRTR2_EL2_Type_nERXGSR_EL1 (← readReg HFGRTR2_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HFGRTR2_EL2_nERXGSR_EL1 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (← readReg ERXGSR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXGSR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXGSR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC0_EL1_SysRegRead_9ea301ebf74aba67 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXMISCn_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXMISCn_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXMISCn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXMISC0_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXMISC0_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXMISC0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC1_EL1_SysRegRead_386d0719bc4739c7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXMISCn_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXMISCn_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXMISCn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXMISC1_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXMISC1_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXMISC1_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC2_EL1_SysRegRead_6ed4c8d1911e048a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXMISCn_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXMISCn_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXMISCn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXMISC2_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXMISC2_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXMISC2_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC3_EL1_SysRegRead_56f8ce5aebf1b5ec (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXMISCn_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXMISCn_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXMISCn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXMISC3_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXMISC3_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXMISC3_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXPFGCDN_EL1_SysRegRead_6e5dee0a1557f09c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIEN ← (( do (pure (_get_SCR_EL3_Type_FIEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FIEN ← (( do (pure (_get_HCR_EL2_Type_FIEN (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXPFGCDN_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXPFGCDN_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIEN == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_FIEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXPFGCDN_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIEN == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXPFGCDN_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIEN == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FIEN == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXPFGCDN_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXPFGCDN_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXPFGCTL_EL1_SysRegRead_420b4fad4c0bef26 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIEN ← (( do (pure (_get_SCR_EL3_Type_FIEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FIEN ← (( do (pure (_get_HCR_EL2_Type_FIEN (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXPFGCTL_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXPFGCTL_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIEN == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_FIEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXPFGCTL_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIEN == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXPFGCTL_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIEN == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FIEN == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXPFGCTL_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXPFGCTL_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXPFGF_EL1_SysRegRead_d0bdc4688b970c59 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIEN ← (( do (pure (_get_SCR_EL3_Type_FIEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FIEN ← (( do (pure (_get_HCR_EL2_Type_FIEN (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXPFGF_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXPFGF_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIEN == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_FIEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXPFGF_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIEN == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXPFGF_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIEN == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FIEN == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXPFGF_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXPFGF_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXSTATUS_EL1_SysRegRead_ca7fd81b70f9297e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ERXSTATUS_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ERXSTATUS_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ERXSTATUS_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg ERXSTATUS_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg ERXSTATUS_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ERXSTATUS_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ESR_EL1_SysRegRead_00d45479b3791ebf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ESR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ESR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ESR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x138#12))))
                  else (X_set t 64 (__get_ESR_EL1 (← readReg ESR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (__get_ESR_EL2 (← readReg ESR_EL2)))
              else (X_set t 64 (__get_ESR_EL1 (← readReg ESR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ESR_EL1 (← readReg ESR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ESR_EL1_SysRegRead_0503f2c5949dd1a4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (__get_ESR_EL1 (← readReg ESR_EL1)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ESR_EL2 (← readReg ESR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ESR_EL2 (← readReg ESR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ESR_EL1_SysRegRead_a03e2d9d46c81b7f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x138#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (__get_ESR_EL1 (← readReg ESR_EL1)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_ESR_EL1 (← readReg ESR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ESR_EL3_SysRegRead_ba1b08f3b6ea1fa7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ESR_EL3 (← readReg ESR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FAR_EL1_SysRegRead_4ac11836ed369460 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x220#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (← readReg FAR_EL1))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg FAR_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FAR_EL2_SysRegRead_49254d82e8554d12 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← readReg FAR_EL1))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg FAR_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg FAR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FAR_EL2_SysRegRead_7a873e0d64ef42a5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_FAR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_FAR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_FAR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x220#12))))
                  else (X_set t 64 (← readReg FAR_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (← readReg FAR_EL2))
              else (X_set t 64 (← readReg FAR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg FAR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FAR_EL3_SysRegRead_5f326570429f53a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg FAR_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FPCR_SysRegRead_48b824e8174adfc0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TFP ← (( do (pure (_get_CPTR_EL3_Type_TFP (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPACR_EL1_FPEN ← (( do (pure (_get_CPACR_EL1_Type_FPEN (← readReg CPACR_EL1))) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_FPEN ← (( do (pure (_get_CPTR_EL2_Type_FPEN (← readReg CPTR_EL2))) ) : SailM (BitVec 2) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TFP ← (( do (pure (_get_CPTR_EL2_Type_TFP (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TFP == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CPACR_EL1_FPEN != 0b11#2)) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x00#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x07#8)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CPTR_EL2_FPEN != 0b11#2)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
              else
                (do
                  if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 1#1)) && (let b__3 := __CPTR_EL2_FPEN
                       if (((Sail.BitVec.extractLsb b__3 0 0) == (0#1 : (BitVec 1))) : Bool)
                       then true
                       else false : Bool)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                  else
                    (do
                      if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H != 1#1)) && (__CPTR_EL2_TFP == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TFP == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8)))
                          else (X_set t 64 (← (__get_FPCR (← readReg FPCR))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TFP == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((let b__2 := __CPACR_EL1_FPEN
                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                 then true
                 else false : Bool) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x07#8))
              else
                (do
                  if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H != 1#1)) && (__CPTR_EL2_TFP == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                  else
                    (do
                      if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 1#1)) && (let b__1 := __CPTR_EL2_FPEN
                           if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TFP == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8)))
                          else (X_set t 64 (← (__get_FPCR (← readReg FPCR)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TFP == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TFP == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_FPEN
                           if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TFP == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8)))
                          else (X_set t 64 (← (__get_FPCR (← readReg FPCR))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_TFP == 1#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))
                  else (X_set t 64 (← (__get_FPCR (← readReg FPCR)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FPEXC32_EL2_SysRegRead_0bed2a86b1b2240d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TFP ← (( do (pure (_get_CPTR_EL3_Type_TFP (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TFP ← (( do (pure (_get_CPTR_EL2_Type_TFP (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_FPEN ← (( do (pure (_get_CPTR_EL2_Type_FPEN (← readReg CPTR_EL2))) ) : SailM (BitVec 2) )
  if ((! (HaveAArch32EL EL1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TFP == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TFP == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                      else
                        (do
                          if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_FPEN
                               if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                               then true
                               else false : Bool)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TFP == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8)))
                              else (X_set t 64 (← (__get_FPEXC32_EL2 (← readReg FPEXC32_EL2))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((__CPTR_EL3_TFP == 1#1) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))
                      else (X_set t 64 (← (__get_FPEXC32_EL2 (← readReg FPEXC32_EL2)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def FPSR_SysRegRead_f0c8f9b942affbc0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TFP ← (( do (pure (_get_CPTR_EL3_Type_TFP (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPACR_EL1_FPEN ← (( do (pure (_get_CPACR_EL1_Type_FPEN (← readReg CPACR_EL1))) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_FPEN ← (( do (pure (_get_CPTR_EL2_Type_FPEN (← readReg CPTR_EL2))) ) : SailM (BitVec 2) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TFP ← (( do (pure (_get_CPTR_EL2_Type_TFP (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TFP == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CPACR_EL1_FPEN != 0b11#2)) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x00#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x07#8)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CPTR_EL2_FPEN != 0b11#2)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
              else
                (do
                  if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 1#1)) && (let b__3 := __CPTR_EL2_FPEN
                       if (((Sail.BitVec.extractLsb b__3 0 0) == (0#1 : (BitVec 1))) : Bool)
                       then true
                       else false : Bool)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                  else
                    (do
                      if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H != 1#1)) && (__CPTR_EL2_TFP == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TFP == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8)))
                          else (X_set t 64 (__get_FPSR (← readReg FPSR)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TFP == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((let b__2 := __CPACR_EL1_FPEN
                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                 then true
                 else false : Bool) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x07#8))
              else
                (do
                  if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H != 1#1)) && (__CPTR_EL2_TFP == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                  else
                    (do
                      if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 1#1)) && (let b__1 := __CPTR_EL2_FPEN
                           if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TFP == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8)))
                          else (X_set t 64 (__get_FPSR (← readReg FPSR))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TFP == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TFP == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_FPEN
                           if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TFP == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8)))
                          else (X_set t 64 (__get_FPSR (← readReg FPSR)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_TFP == 1#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))
                  else (X_set t 64 (__get_FPSR (← readReg FPSR))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCR_EL1_SysRegRead_62bd5315db9a2829 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ATA ← (( do (pure (_get_SCR_EL3_Type_ATA (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_ATA ← (( do (pure (_get_HCR_EL2_Type_ATA (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_ATA == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_ATA == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_ATA == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_GCR_EL1 (← readReg GCR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_ATA == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_ATA == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_GCR_EL1 (← readReg GCR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GCR_EL1 (← readReg GCR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSCRE0_EL1_SysRegRead_0250ee8c94b04721 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nGCS_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_nGCS_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nGCS_EL0 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_GCSCRE0_EL1 (← readReg GCSCRE0_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_GCSCRE0_EL1 (← readReg GCSCRE0_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GCSCRE0_EL1 (← readReg GCSCRE0_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSCR_EL1_SysRegRead_a1c1abc2b55fb304 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x8D0#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_GCSCR_EL1 (← readReg GCSCR_EL1)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_GCSCR_EL1 (← readReg GCSCR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSCR_EL1_SysRegRead_c10918a3ea4a2f5c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nGCS_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nGCS_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nGCS_EL1 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                      then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x8D0#12))))
                      else (X_set t 64 (__get_GCSCR_EL1 (← readReg GCSCR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (__get_GCSCR_EL2 (← readReg GCSCR_EL2)))
                      else (X_set t 64 (__get_GCSCR_EL1 (← readReg GCSCR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GCSCR_EL1 (← readReg GCSCR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSCR_EL2_SysRegRead_cc7b26a3631eab6f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_GCSCR_EL2 (← readReg GCSCR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GCSCR_EL2 (← readReg GCSCR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSCR_EL3_SysRegRead_f722c361b12a49bd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GCSCR_EL3 (← readReg GCSCR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPR_EL0_SysRegRead_eb4ca18a2cca83d6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __GCSCRE0_EL1_nTR ← (( do (pure (_get_GCSCRE0_EL1_Type_nTR (← readReg GCSCRE0_EL1))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nGCS_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_nGCS_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((((! (← (EL2Enabled ()))) || (__HCR_EL2_TGE != 1#1)) && (__GCSCRE0_EL1_nTR == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) && (__GCSCRE0_EL1_nTR == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nGCS_EL0 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_GCSPR_EL0 (← readReg GCSPR_EL0))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nGCS_EL0 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_GCSPR_EL0 (← readReg GCSPR_EL0))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_GCSPR_EL0 (← readReg GCSPR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GCSPR_EL0 (← readReg GCSPR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPR_EL1_SysRegRead_474789c62224c972 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x8C0#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_GCSPR_EL1 (← readReg GCSPR_EL1)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_GCSPR_EL1 (← readReg GCSPR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPR_EL1_SysRegRead_efbe68095a628d64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nGCS_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nGCS_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nGCS_EL1 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                      then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x8C0#12))))
                      else (X_set t 64 (__get_GCSPR_EL1 (← readReg GCSPR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (__get_GCSPR_EL2 (← readReg GCSPR_EL2)))
                      else (X_set t 64 (__get_GCSPR_EL1 (← readReg GCSPR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GCSPR_EL1 (← readReg GCSPR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPR_EL2_SysRegRead_9daadab9c1c453f3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_GCSPR_EL2 (← readReg GCSPR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GCSPR_EL2 (← readReg GCSPR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPR_EL3_SysRegRead_3f6b8f8e31fb3882 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GCSPR_EL3 (← readReg GCSPR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GMID_EL1_SysRegRead_df65333e6c977d08 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID5 ← (( do (pure (_get_HCR_EL2_Type_TID5 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID5 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_GMID_EL1 (← readReg GMID_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_GMID_EL1 (← readReg GMID_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GMID_EL1 (← readReg GMID_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GPCCR_EL3_SysRegRead_709f878e2648a87d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GPCCR_EL3 (← readReg GPCCR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GPTBR_EL3_SysRegRead_fe0f38a8cd7c60a9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_GPTBR_EL3 (← readReg GPTBR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HACR_EL2_SysRegRead_d6fb34f6f0d841c4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg HACR_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg HACR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HAFGRTR_EL2_SysRegRead_b9d391a626b7035e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1E8#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HAFGRTR_EL2 (← readReg HAFGRTR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HAFGRTR_EL2 (← readReg HAFGRTR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HCRX_EL2_SysRegRead_ac90b414dcf6527a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_HXEn ← (( do (pure (_get_SCR_EL3_Type_HXEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0xA0#8))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_HXEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_HXEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HCRX_EL2 (← readReg HCRX_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HCRX_EL2 (← readReg HCRX_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HCR_EL2_SysRegRead_5224f361c75e16cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x078#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg HCR_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg HCR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HDFGRTR2_EL2_SysRegRead_fb9db770ba4c3bae (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1A0#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HDFGRTR2_EL2 (← readReg HDFGRTR2_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HDFGRTR2_EL2 (← readReg HDFGRTR2_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HDFGRTR_EL2_SysRegRead_2c14bf21b897a1bb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1D0#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HDFGRTR_EL2 (← readReg HDFGRTR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HDFGRTR_EL2 (← readReg HDFGRTR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HDFGWTR2_EL2_SysRegRead_5781127e61739817 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1B0#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HDFGWTR2_EL2 (← readReg HDFGWTR2_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HDFGWTR2_EL2 (← readReg HDFGWTR2_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HDFGWTR_EL2_SysRegRead_c6796c2a296d66f8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1D8#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HDFGWTR_EL2 (← readReg HDFGWTR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HDFGWTR_EL2 (← readReg HDFGWTR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGITR2_EL2_SysRegRead_9589905774d1f5d8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x310#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HFGITR2_EL2 (← readReg HFGITR2_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HFGITR2_EL2 (← readReg HFGITR2_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGITR_EL2_SysRegRead_2ac6d936359d43d5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1C8#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HFGITR_EL2 (← readReg HFGITR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HFGITR_EL2 (← readReg HFGITR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGRTR2_EL2_SysRegRead_e34348a8454b3058 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x2C0#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HFGRTR2_EL2 (← readReg HFGRTR2_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HFGRTR2_EL2 (← readReg HFGRTR2_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGRTR_EL2_SysRegRead_2d8c69ae2f7682c6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1B8#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HFGRTR_EL2 (← readReg HFGRTR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HFGRTR_EL2 (← readReg HFGRTR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGWTR2_EL2_SysRegRead_67317c38f0a466b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x2C8#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HFGWTR2_EL2 (← readReg HFGWTR2_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HFGWTR2_EL2 (← readReg HFGWTR2_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGWTR_EL2_SysRegRead_efd0bbb67b091b14 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1C0#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_FGTEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_HFGWTR_EL2 (← readReg HFGWTR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HFGWTR_EL2 (← readReg HFGWTR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HPFAR_EL2_SysRegRead_9238fb9a3f4fb1bb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_HPFAR_EL2 (← readReg HPFAR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HPFAR_EL2 (← readReg HPFAR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HSTR_EL2_SysRegRead_4e780f9f195cb950 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x080#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_HSTR_EL2 (← readReg HSTR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_HSTR_EL2 (← readReg HSTR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_AP0R_EL1_SysRegRead_4af9bde7d3ab9efe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICC_AP0R_EL1_SysRegRead_51434e4b9d244793 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICC_AP0R_EL1_SysRegRead_c5e122be1753fb85 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_AP0R_EL1 (GetElem?.getElem! (← readReg ICV_AP0R_EL1) 0)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_ICC_AP0R_EL1 (GetElem?.getElem! (← readReg ICC_AP0R_EL1) 0))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ICC_AP0R_EL1 (GetElem?.getElem! (← readReg ICC_AP0R_EL1) 0))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_AP0R_EL1 (GetElem?.getElem! (← readReg ICC_AP0R_EL1) 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_AP0R_EL1_SysRegRead_c718785136d493b9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICC_AP1R_EL1_SysRegRead_39371d4468952849 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICC_AP1R_EL1_SysRegRead_5a702399a390f8ec (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICC_AP1R_EL1_SysRegRead_6535748ba14d930e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICC_AP1R_EL1_SysRegRead_a0d3f3e1a65fa7f7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_AP1R_EL1 (GetElem?.getElem! (← readReg ICV_AP1R_EL1) 0)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((HaveEL EL3) : Bool)
                              then
                                (do
                                  if ((__SCR_EL3_NS == 0#1) : Bool)
                                  then (X_set t 64 (__get_ICC_AP1R_EL1_S (GetElem?.getElem! (← readReg ICC_AP1R_EL1_S) 0)))
                                  else (X_set t 64 (__get_ICC_AP1R_EL1_NS (GetElem?.getElem! (← readReg ICC_AP1R_EL1_NS) 0))))
                              else (X_set t 64 (__get_ICC_AP1R_EL1 (← (ICC_AP1R_EL1_read 0))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((HaveEL EL3) : Bool)
                          then
                            (do
                              if ((__SCR_EL3_NS == 0#1) : Bool)
                              then (X_set t 64 (__get_ICC_AP1R_EL1_S (GetElem?.getElem! (← readReg ICC_AP1R_EL1_S) 0)))
                              else (X_set t 64 (__get_ICC_AP1R_EL1_NS (GetElem?.getElem! (← readReg ICC_AP1R_EL1_NS) 0))))
                          else (X_set t 64 (__get_ICC_AP1R_EL1 (← (ICC_AP1R_EL1_read 0))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((__SCR_EL3_NS == 0#1) : Bool)
                      then (X_set t 64 (__get_ICC_AP1R_EL1_S (GetElem?.getElem! (← readReg ICC_AP1R_EL1_S) 0)))
                      else (X_set t 64 (__get_ICC_AP1R_EL1_NS (GetElem?.getElem! (← readReg ICC_AP1R_EL1_NS) 0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_BPR0_EL1_SysRegRead_b8c7d452ff7b9c66 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_BPR0_EL1 (← readReg ICV_BPR0_EL1)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_ICC_BPR0_EL1 (← readReg ICC_BPR0_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ICC_BPR0_EL1 (← readReg ICC_BPR0_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_BPR0_EL1 (← readReg ICC_BPR0_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_CTLR_EL1_SysRegRead_eb1de12df33d5c37 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TC ← (( do (pure (_get_ICH_HCR_EL2_Type_TC (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TC == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_CTLR_EL1 (← readReg ICV_CTLR_EL1)))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                          then (X_set t 64 (__get_ICV_CTLR_EL1 (← readReg ICV_CTLR_EL1)))
                          else
                            (do
                              if ((←((pure (HaveEL EL3)) <&&> (do
                                   (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if ((HaveEL EL3) : Bool)
                                  then
                                    (do
                                      if ((__SCR_EL3_NS == 0#1) : Bool)
                                      then (X_set t 64 (__get_ICC_CTLR_EL1_S (← readReg ICC_CTLR_EL1_S)))
                                      else (X_set t 64 (__get_ICC_CTLR_EL1_NS (← readReg ICC_CTLR_EL1_NS))))
                                  else (X_set t 64 (__get_ICC_CTLR_EL1 (← (ICC_CTLR_EL1_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((HaveEL EL3) : Bool)
                          then
                            (do
                              if ((__SCR_EL3_NS == 0#1) : Bool)
                              then (X_set t 64 (__get_ICC_CTLR_EL1_S (← readReg ICC_CTLR_EL1_S)))
                              else (X_set t 64 (__get_ICC_CTLR_EL1_NS (← readReg ICC_CTLR_EL1_NS))))
                          else (X_set t 64 (__get_ICC_CTLR_EL1 (← (ICC_CTLR_EL1_read ()))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((__SCR_EL3_NS == 0#1) : Bool)
                      then (X_set t 64 (__get_ICC_CTLR_EL1_S (← readReg ICC_CTLR_EL1_S)))
                      else (X_set t 64 (__get_ICC_CTLR_EL1_NS (← readReg ICC_CTLR_EL1_NS)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_CTLR_EL3_SysRegRead_7a137fb26d669941 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_CTLR_EL3 (← readReg ICC_CTLR_EL3))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_HPPIR0_EL1_SysRegRead_03eb902d5ba703ac (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_HPPIR0_EL1 (← readReg ICV_HPPIR0_EL1)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_ICC_HPPIR0_EL1 (← readReg ICC_HPPIR0_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ICC_HPPIR0_EL1 (← readReg ICC_HPPIR0_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_HPPIR0_EL1 (← readReg ICC_HPPIR0_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_HPPIR1_EL1_SysRegRead_49e183ca83eb8361 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_HPPIR1_EL1 (← readReg ICV_HPPIR1_EL1)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_ICC_HPPIR1_EL1 (← readReg ICC_HPPIR1_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ICC_HPPIR1_EL1 (← readReg ICC_HPPIR1_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_HPPIR1_EL1 (← readReg ICC_HPPIR1_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_IGRPEN0_EL1_SysRegRead_5872e0ee48947240 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ICC_IGRPENn_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ICC_IGRPENn_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ICC_IGRPENn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_FMO == 1#1)) : Bool)
                          then (X_set t 64 (__get_ICV_IGRPEN0_EL1 (← readReg ICV_IGRPEN0_EL1)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else (X_set t 64 (__get_ICC_IGRPEN0_EL1 (← readReg ICC_IGRPEN0_EL1)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ICC_IGRPEN0_EL1 (← readReg ICC_IGRPEN0_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_IGRPEN0_EL1 (← readReg ICC_IGRPEN0_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_IGRPEN1_EL1_SysRegRead_91fcd06cccdfe885 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ICC_IGRPENn_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ICC_IGRPENn_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ICC_IGRPENn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                          then (X_set t 64 (__get_ICV_IGRPEN1_EL1 (← readReg ICV_IGRPEN1_EL1)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if ((HaveEL EL3) : Bool)
                                  then
                                    (do
                                      if ((__SCR_EL3_NS == 0#1) : Bool)
                                      then (X_set t 64 (__get_ICC_IGRPEN1_EL1_S (← readReg ICC_IGRPEN1_EL1_S)))
                                      else (X_set t 64 (__get_ICC_IGRPEN1_EL1_NS (← readReg ICC_IGRPEN1_EL1_NS))))
                                  else (X_set t 64 (__get_ICC_IGRPEN1_EL1 (← (ICC_IGRPEN1_EL1_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((HaveEL EL3) : Bool)
                          then
                            (do
                              if ((__SCR_EL3_NS == 0#1) : Bool)
                              then (X_set t 64 (__get_ICC_IGRPEN1_EL1_S (← readReg ICC_IGRPEN1_EL1_S)))
                              else (X_set t 64 (__get_ICC_IGRPEN1_EL1_NS (← readReg ICC_IGRPEN1_EL1_NS))))
                          else (X_set t 64 (__get_ICC_IGRPEN1_EL1 (← (ICC_IGRPEN1_EL1_read ()))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((__SCR_EL3_NS == 0#1) : Bool)
                      then (X_set t 64 (__get_ICC_IGRPEN1_EL1_S (← readReg ICC_IGRPEN1_EL1_S)))
                      else (X_set t 64 (__get_ICC_IGRPEN1_EL1_NS (← readReg ICC_IGRPEN1_EL1_NS)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_IGRPEN1_EL3_SysRegRead_36d699c35dbd8f69 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_IGRPEN1_EL3 (← readReg ICC_IGRPEN1_EL3))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_PMR_EL1_SysRegRead_538510958f22076c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TC ← (( do (pure (_get_ICH_HCR_EL2_Type_TC (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TC == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_PMR_EL1 (← readReg ICV_PMR_EL1)))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                          then (X_set t 64 (__get_ICV_PMR_EL1 (← readReg ICV_PMR_EL1)))
                          else
                            (do
                              if ((←((pure (HaveEL EL3)) <&&> (do
                                   (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else (X_set t 64 (__get_ICC_PMR_EL1 (← readReg ICC_PMR_EL1)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ICC_PMR_EL1 (← readReg ICC_PMR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_PMR_EL1 (← readReg ICC_PMR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_RPR_EL1_SysRegRead_ed1234736c835707 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TC ← (( do (pure (_get_ICH_HCR_EL2_Type_TC (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TC == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_RPR_EL1 (← readReg ICV_RPR_EL1)))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                          then (X_set t 64 (__get_ICV_RPR_EL1 (← readReg ICV_RPR_EL1)))
                          else
                            (do
                              if ((←((pure (HaveEL EL3)) <&&> (do
                                   (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else (X_set t 64 (__get_ICC_RPR_EL1 (← readReg ICC_RPR_EL1)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ICC_RPR_EL1 (← readReg ICC_RPR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_RPR_EL1 (← readReg ICC_RPR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_SRE_EL1_SysRegRead_66e16dcbec736265 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_Enable ← (( do (pure (_get_ICC_SRE_EL3_Type_Enable (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_Enable ← (( do (pure (_get_ICC_SRE_EL2_Type_Enable (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__ICC_SRE_EL2_Enable == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((HaveEL EL3) : Bool)
                      then
                        (do
                          if ((__SCR_EL3_NS == 0#1) : Bool)
                          then (X_set t 64 (__get_ICC_SRE_EL1_S (← readReg ICC_SRE_EL1_S)))
                          else (X_set t 64 (__get_ICC_SRE_EL1_NS (← readReg ICC_SRE_EL1_NS))))
                      else (X_set t 64 (__get_ICC_SRE_EL1 (← (ICC_SRE_EL1_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((HaveEL EL3) : Bool)
                      then
                        (do
                          if ((__SCR_EL3_NS == 0#1) : Bool)
                          then (X_set t 64 (__get_ICC_SRE_EL1_S (← readReg ICC_SRE_EL1_S)))
                          else (X_set t 64 (__get_ICC_SRE_EL1_NS (← readReg ICC_SRE_EL1_NS))))
                      else (X_set t 64 (__get_ICC_SRE_EL1 (← (ICC_SRE_EL1_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (X_set t 64 (__get_ICC_SRE_EL1_S (← readReg ICC_SRE_EL1_S)))
                  else (X_set t 64 (__get_ICC_SRE_EL1_NS (← readReg ICC_SRE_EL1_NS))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_SRE_EL2_SysRegRead_7b340e47907381fb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_Enable ← (( do (pure (_get_ICC_SRE_EL3_Type_Enable (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_ICC_SRE_EL2 (← readReg ICC_SRE_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (__get_ICC_SRE_EL2 (← readReg ICC_SRE_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_SRE_EL3_SysRegRead_7a177b6c72e9cd7e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ICC_SRE_EL3 (← readReg ICC_SRE_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_AP0R_EL2_SysRegRead_52a53932b4c339f0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP0R_EL2_SysRegRead_59f0de8946000971 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP0R_EL2_SysRegRead_5c5dde09d918dae7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x480#12) +i (8 *i 0)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_AP0R_EL2 (GetElem?.getElem! (← readReg ICH_AP0R_EL2) 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_AP0R_EL2 (GetElem?.getElem! (← readReg ICH_AP0R_EL2) 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_AP0R_EL2_SysRegRead_e9c19cba17805bc5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_EL2_SysRegRead_30ea39c810423a08 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_EL2_SysRegRead_6e9c00e7ee655a1c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_EL2_SysRegRead_7e396ec20ce46cc8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_EL2_SysRegRead_c149792475ac1b5e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x4A0#12) +i (8 *i 0)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_AP1R_EL2 (GetElem?.getElem! (← readReg ICH_AP1R_EL2) 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_AP1R_EL2 (GetElem?.getElem! (← readReg ICH_AP1R_EL2) 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_EISR_EL2_SysRegRead_b94071bbed7793e6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_EISR_EL2 (← readReg ICH_EISR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_EISR_EL2 (← readReg ICH_EISR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_ELRSR_EL2_SysRegRead_f3283fecb3432702 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_ELRSR_EL2 (← readReg ICH_ELRSR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_ELRSR_EL2 (← readReg ICH_ELRSR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_HCR_EL2_SysRegRead_2d127848d9701956 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x4C0#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_HCR_EL2 (← readReg ICH_HCR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_HCR_EL2 (← readReg ICH_HCR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_4e742d1e920f7e6a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 7)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 7))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 7))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_5892cb2908346b8f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 8)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 8))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 8))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_699f2fe4ff960178 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 2)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_6fc0cefa24d83ad7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 3)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 3))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 3))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_760236e55a89ef60 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 0)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_77cba5409a6a519d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 4)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 4))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 4))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_7b5788e0eea7d16d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 9)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 9))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 9))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_7b87e2c873df96d3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 15)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 15))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 15))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_9bbb7ed062f56571 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 11)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 11))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 11))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_a618297619bdffa8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 6)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 6))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 6))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_acbe44db6613ec59 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 12)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 12))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 12))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_aea95b9712305e61 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 10)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 10))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 10))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_b2fb82f050f6bc86 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 1)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_c81d0fe793ef58d2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 14)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 14))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 14))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_f0dfb1b6bea2d67b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 13)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 13))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 13))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegRead_fa3ca488734d3bcc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0x400#12) +i (8 *i 5)))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 5))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_LR_EL2 (GetElem?.getElem! (← readReg ICH_LR_EL2) 5))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_MISR_EL2_SysRegRead_c4aa5214cb9e1506 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_MISR_EL2 (← readReg ICH_MISR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_MISR_EL2 (← readReg ICH_MISR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_VMCR_EL2_SysRegRead_7485c707cb4a586a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x4C8#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_VMCR_EL2 (← readReg ICH_VMCR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_VMCR_EL2 (← readReg ICH_VMCR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_VTR_EL2_SysRegRead_35151b955e524a69 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_ICH_VTR_EL2 (← readReg ICH_VTR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICH_VTR_EL2 (← readReg ICH_VTR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_BPR1_EL1_SysRegRead_3b949083543338aa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_BPR1_EL1 (← readReg ICV_BPR1_EL1)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((HaveEL EL3) : Bool)
                              then
                                (do
                                  if ((__SCR_EL3_NS == 0#1) : Bool)
                                  then (X_set t 64 (__get_ICC_BPR1_EL1_S (← readReg ICC_BPR1_EL1_S)))
                                  else (X_set t 64 (__get_ICC_BPR1_EL1_NS (← readReg ICC_BPR1_EL1_NS))))
                              else (X_set t 64 (__get_ICC_BPR1_EL1 (← (ICC_BPR1_EL1_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((HaveEL EL3) : Bool)
                          then
                            (do
                              if ((__SCR_EL3_NS == 0#1) : Bool)
                              then (X_set t 64 (__get_ICC_BPR1_EL1_S (← readReg ICC_BPR1_EL1_S)))
                              else (X_set t 64 (__get_ICC_BPR1_EL1_NS (← readReg ICC_BPR1_EL1_NS))))
                          else (X_set t 64 (__get_ICC_BPR1_EL1 (← (ICC_BPR1_EL1_read ()))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((__SCR_EL3_NS == 0#1) : Bool)
                      then (X_set t 64 (__get_ICC_BPR1_EL1_S (← readReg ICC_BPR1_EL1_S)))
                      else (X_set t 64 (__get_ICC_BPR1_EL1_NS (← readReg ICC_BPR1_EL1_NS)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_IAR0_EL1_SysRegRead_8bcb4b4c3394a634 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_IAR0_EL1 (← readReg ICV_IAR0_EL1)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_ICC_IAR0_EL1 (← readReg ICC_IAR0_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ICC_IAR0_EL1 (← readReg ICC_IAR0_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_IAR0_EL1 (← readReg ICC_IAR0_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_IAR1_EL1_SysRegRead_e78579ad210f1e05 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                      then (X_set t 64 (__get_ICV_IAR1_EL1 (← readReg ICV_IAR1_EL1)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_ICC_IAR1_EL1 (← readReg ICC_IAR1_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_ICC_IAR1_EL1 (← readReg ICC_IAR1_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_ICC_IAR1_EL1 (← readReg ICC_IAR1_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_NMIAR1_EL1_SysRegRead_fc1b7cc86475bbcb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_NMI ← (( do (pure (_get_SCTLR_EL1_Type_NMI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_NMI ← (( do (pure (_get_SCTLR_EL2_Type_NMI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL3_NMI ← (( do (pure (_get_SCTLR_EL3_Type_NMI (← readReg SCTLR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((__SCTLR_EL1_NMI == 0#1) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                          then (X_set t 64 (__get_ICV_NMIAR1_EL1 (← readReg ICV_NMIAR1_EL1)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else (X_set t 64 (__get_ICC_NMIAR1_EL1 (← readReg ICC_NMIAR1_EL1)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__SCTLR_EL2_NMI == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_ICC_NMIAR1_EL1 (← readReg ICC_NMIAR1_EL1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCTLR_EL3_NMI == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else (X_set t 64 (__get_ICC_NMIAR1_EL1 (← readReg ICC_NMIAR1_EL1)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64AFR0_EL1_SysRegRead_d690252709f00b61 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64AFR0_EL1 (← readReg ID_AA64AFR0_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64AFR0_EL1 (← readReg ID_AA64AFR0_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64AFR0_EL1 (← readReg ID_AA64AFR0_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64AFR1_EL1_SysRegRead_1072eb4f153853b5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64AFR1_EL1 (← readReg ID_AA64AFR1_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64AFR1_EL1 (← readReg ID_AA64AFR1_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64AFR1_EL1 (← readReg ID_AA64AFR1_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64DFR0_EL1_SysRegRead_2534c3350994a417 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_AA64DFR0_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_AA64DFR0_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_AA64DFR0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64DFR1_EL1_SysRegRead_efaff2fa63cea9e4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_AA64DFR1_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_AA64DFR1_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_AA64DFR1_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64ISAR0_EL1_SysRegRead_bbc5747e80790ed5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← (__get_ID_AA64ISAR0_EL1 (← readReg ID_AA64ISAR0_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← (__get_ID_AA64ISAR0_EL1 (← readReg ID_AA64ISAR0_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (__get_ID_AA64ISAR0_EL1 (← readReg ID_AA64ISAR0_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64ISAR1_EL1_SysRegRead_5f004fea0c608df9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_AA64ISAR1_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_AA64ISAR1_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_AA64ISAR1_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64ISAR2_EL1_SysRegRead_c585336ab0c39b5d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_AA64ISAR2_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_AA64ISAR2_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64ISAR2_EL1 (← readReg ID_AA64ISAR2_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64ISAR2_EL1 (← readReg ID_AA64ISAR2_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64ISAR2_EL1 (← readReg ID_AA64ISAR2_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64MMFR0_EL1_SysRegRead_52d0be9703325603 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64MMFR0_EL1 (← readReg ID_AA64MMFR0_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64MMFR0_EL1 (← readReg ID_AA64MMFR0_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64MMFR0_EL1 (← readReg ID_AA64MMFR0_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64MMFR1_EL1_SysRegRead_8e0c46321a1a5a47 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_AA64MMFR1_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_AA64MMFR1_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_AA64MMFR1_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64MMFR2_EL1_SysRegRead_cc8ba5aa21a8fd21 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_AA64MMFR2_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_AA64MMFR2_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64MMFR2_EL1 (← readReg ID_AA64MMFR2_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64MMFR2_EL1 (← readReg ID_AA64MMFR2_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64MMFR2_EL1 (← readReg ID_AA64MMFR2_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64MMFR3_EL1_SysRegRead_a84482354ffb3943 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_AA64MMFR3_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_AA64MMFR3_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64MMFR3_EL1 (← readReg ID_AA64MMFR3_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64MMFR3_EL1 (← readReg ID_AA64MMFR3_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64MMFR3_EL1 (← readReg ID_AA64MMFR3_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64MMFR4_EL1_SysRegRead_3578f169e732088b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_AA64MMFR4_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_AA64MMFR4_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64MMFR4_EL1 (← readReg ID_AA64MMFR4_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64MMFR4_EL1 (← readReg ID_AA64MMFR4_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64MMFR4_EL1 (← readReg ID_AA64MMFR4_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64PFR0_EL1_SysRegRead_f36f783e888272fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_AA64PFR0_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_AA64PFR0_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_AA64PFR0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64PFR1_EL1_SysRegRead_99547bac83e88d23 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64PFR1_EL1 (← readReg ID_AA64PFR1_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64PFR1_EL1 (← readReg ID_AA64PFR1_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64PFR1_EL1 (← readReg ID_AA64PFR1_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64PFR2_EL1_SysRegRead_c98524f93c119d97 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_AA64PFR2_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_AA64PFR2_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64PFR2_EL1 (← readReg ID_AA64PFR2_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64PFR2_EL1 (← readReg ID_AA64PFR2_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64PFR2_EL1 (← readReg ID_AA64PFR2_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64SMFR0_EL1_SysRegRead_8f4054d57f9da064 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_AA64SMFR0_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_AA64SMFR0_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64SMFR0_EL1 (← readReg ID_AA64SMFR0_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64SMFR0_EL1 (← readReg ID_AA64SMFR0_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64SMFR0_EL1 (← readReg ID_AA64SMFR0_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AA64ZFR0_EL1_SysRegRead_dd573310e3efc3be (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_AA64ZFR0_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_AA64ZFR0_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ID_AA64ZFR0_EL1 (← readReg ID_AA64ZFR0_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ID_AA64ZFR0_EL1 (← readReg ID_AA64ZFR0_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ID_AA64ZFR0_EL1 (← readReg ID_AA64ZFR0_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_AFR0_EL1_SysRegRead_8cb989b34cb8a122 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_AFR0_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_AFR0_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_AFR0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_DFR0_EL1_SysRegRead_fd3ff6eac0bbb4f5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_DFR0_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_DFR0_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_DFR0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_DFR1_EL1_SysRegRead_de4a2c9fc10617db (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_DFR1_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_DFR1_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_DFR1_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_DFR1_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_DFR1_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_ISAR0_EL1_SysRegRead_24c5894e067c2865 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_ISAR0_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_ISAR0_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_ISAR0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_ISAR1_EL1_SysRegRead_659998c6404a0adc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_ISAR1_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_ISAR1_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_ISAR1_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_ISAR2_EL1_SysRegRead_b7383eed8683183b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_ISAR2_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_ISAR2_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_ISAR2_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_ISAR3_EL1_SysRegRead_e32f388e1b8f6c5e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_ISAR3_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_ISAR3_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_ISAR3_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_ISAR4_EL1_SysRegRead_b41d0fd5cce0f813 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_ISAR4_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_ISAR4_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_ISAR4_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_ISAR5_EL1_SysRegRead_7b34ff950445f0bc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_ISAR5_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_ISAR5_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_ISAR5_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_ISAR6_EL1_SysRegRead_c5d967e39ea7cb96 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_ISAR6_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_ISAR6_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_ISAR6_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_ISAR6_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_ISAR6_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_MMFR0_EL1_SysRegRead_911dfac1545c3c44 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_MMFR0_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_MMFR0_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_MMFR0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_MMFR1_EL1_SysRegRead_5bc0d8918ab34ceb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_MMFR1_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_MMFR1_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_MMFR1_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_MMFR2_EL1_SysRegRead_8d15523f6def058f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_MMFR2_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_MMFR2_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_MMFR2_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_MMFR3_EL1_SysRegRead_a9cd04d27834c148 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_MMFR3_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_MMFR3_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_MMFR3_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_MMFR4_EL1_SysRegRead_f8caea53c1015428 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_MMFR4_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_MMFR4_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_MMFR4_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_MMFR4_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_MMFR4_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_MMFR5_EL1_SysRegRead_aa9b432015ad78b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_MMFR5_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_MMFR5_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_MMFR5_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_MMFR5_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_MMFR5_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_PFR0_EL1_SysRegRead_51a48b3c62008265 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_PFR0_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_PFR0_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_PFR0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_PFR1_EL1_SysRegRead_0333fe2887e1adfd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_PFR1_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_PFR1_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_PFR1_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ID_PFR2_EL1_SysRegRead_d9584bfc0ea04005 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsFeatureImplemented FEAT_FGT) <||> (do
                   (pure (! (IsZero (← readReg ID_PFR2_EL1))))) <||> (do
                   (__IMPDEF_boolean "ID_PFR2_EL1 trapped by HCR_EL2.TID3"))))) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg ID_PFR2_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ID_PFR2_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ID_PFR2_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def IFSR32_EL2_SysRegRead_bc5173df6fb29c65 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((! (HaveAArch32EL EL1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (X_set t 64 (__get_IFSR32_EL2 (← readReg IFSR32_EL2)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_IFSR32_EL2 (← readReg IFSR32_EL2)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def ISR_EL1_SysRegRead_9452dc797f0bae53 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_ISR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_ISR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_ISR_EL1 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_ISR_EL1 (← readReg ISR_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_ISR_EL1 (← readReg ISR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ISR_EL1 (← readReg ISR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def LORC_EL1_SysRegRead_50b423e6e0102ba8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TLOR ← (( do (pure (_get_SCR_EL3_Type_TLOR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TLOR ← (( do (pure (_get_HCR_EL2_Type_TLOR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_LORC_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_LORC_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TLOR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TLOR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_LORC_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_LORC_EL1 (← readReg LORC_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_LORC_EL1 (← readReg LORC_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (__get_LORC_EL1 (← readReg LORC_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def LOREA_EL1_SysRegRead_c69af0a70feec9d7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TLOR ← (( do (pure (_get_SCR_EL3_Type_TLOR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TLOR ← (( do (pure (_get_HCR_EL2_Type_TLOR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_LOREA_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_LOREA_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TLOR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TLOR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_LOREA_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_LOREA_EL1 (← readReg LOREA_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_LOREA_EL1 (← readReg LOREA_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (__get_LOREA_EL1 (← readReg LOREA_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def LORID_EL1_SysRegRead_3eb3572baf1f9d7d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TLOR ← (( do (pure (_get_SCR_EL3_Type_TLOR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TLOR ← (( do (pure (_get_HCR_EL2_Type_TLOR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_LORID_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_LORID_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TLOR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TLOR == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_LORID_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_LORID_EL1 (← readReg LORID_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TLOR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_LORID_EL1 (← readReg LORID_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_LORID_EL1 (← readReg LORID_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def LORN_EL1_SysRegRead_f1da155c7f7014b9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TLOR ← (( do (pure (_get_SCR_EL3_Type_TLOR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TLOR ← (( do (pure (_get_HCR_EL2_Type_TLOR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_LORN_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_LORN_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TLOR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TLOR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_LORN_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_LORN_EL1 (← readReg LORN_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_LORN_EL1 (← readReg LORN_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (__get_LORN_EL1 (← readReg LORN_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def LORSA_EL1_SysRegRead_eff0a73c3cb651d8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TLOR ← (( do (pure (_get_SCR_EL3_Type_TLOR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TLOR ← (( do (pure (_get_HCR_EL2_Type_TLOR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_LORSA_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_LORSA_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TLOR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TLOR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_LORSA_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_LORSA_EL1 (← readReg LORSA_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_LORSA_EL1 (← readReg LORSA_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (__get_LORSA_EL1 (← readReg LORSA_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR2_EL1_SysRegRead_5817d7d1bdb094d0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AIEn ← (( do (pure (_get_SCR_EL3_Type_AIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x280#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AIEn == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_AIEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg MAIR2_EL1))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg MAIR2_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR2_EL2_SysRegRead_64c24db4df3eb258 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AIEn ← (( do (pure (_get_SCR_EL3_Type_AIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nMAIR2_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nMAIR2_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AIEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nMAIR2_EL1 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_AIEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x280#12))))
                          else (X_set t 64 (← readReg MAIR2_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AIEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_AIEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (← readReg MAIR2_EL2))
                      else (X_set t 64 (← readReg MAIR2_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MAIR2_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR2_EL2_SysRegRead_88d9ce00117fb633 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AIEn ← (( do (pure (_get_SCR_EL3_Type_AIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AIEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_AIEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg MAIR2_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MAIR2_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR2_EL3_SysRegRead_06e8ce86a19999af (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MAIR2_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR_EL1_SysRegRead_66ca2d8fc428dd45 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_MAIR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_MAIR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_MAIR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x140#12))))
                  else (X_set t 64 (← readReg MAIR_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (← readReg MAIR_EL2))
              else (X_set t 64 (← readReg MAIR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MAIR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR_EL1_SysRegRead_f6ee03bc53b980dd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x140#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (← readReg MAIR_EL1))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg MAIR_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR_EL2_SysRegRead_c37e0065b9939c9e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg MAIR_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MAIR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR_EL3_SysRegRead_3a3602f6f0c9e03f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MAIR_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MDCCINT_EL1_SysRegRead_8ab11d15362084e3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((Halted ()) <&&> (do
           (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
      then (X_set t 64 (__get_MDCCINT_EL1 (← readReg MDCCINT_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                  then
                                    (do
                                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else (X_set t 64 (__get_MDCCINT_EL1 (← readReg MDCCINT_EL1)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else (X_set t 64 (__get_MDCCINT_EL1 (← readReg MDCCINT_EL1)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_MDCCINT_EL1 (← readReg MDCCINT_EL1)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def MDCCSR_EL0_SysRegRead_01ce581683168bc2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((←((Halted ()) <&&> (do
       (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
  then (X_set t 64 (__get_MDCCSR_EL0 (← readReg MDCCSR_EL0)))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__MDSCR_EL1_TDCC == 1#1) : Bool)
                  then
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do
                                 (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2)))))) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                  then
                                    (do
                                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else (X_set t 64 (__get_MDCCSR_EL0 (← readReg MDCCSR_EL0))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                  then
                                    (do
                                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else (X_set t 64 (__get_MDCCSR_EL0 (← readReg MDCCSR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else (X_set t 64 (__get_MDCCSR_EL0 (← readReg MDCCSR_EL0)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_MDCCSR_EL0 (← readReg MDCCSR_EL0)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def MDCR_EL2_SysRegRead_b8f16b372834c035 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_MDCR_EL2 (← readReg MDCR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MDCR_EL2 (← readReg MDCR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MDCR_EL3_SysRegRead_fa75e32e1a0e4d27 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MDCR_EL3 (← readReg MDCR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MDRAR_EL1_SysRegRead_9bbd6b527037e7d1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDRA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_MDRAR_EL1 (← readReg MDRAR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_MDRAR_EL1 (← readReg MDRAR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MDRAR_EL1 (← readReg MDRAR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MDSCR_EL1_SysRegRead_cf631f2b4ddd25e0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_MDSCR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_MDSCR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_MDSCR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x158#12))))
                          else (X_set t 64 (__get_MDSCR_EL1 (← readReg MDSCR_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_MDSCR_EL1 (← readReg MDSCR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MDSCR_EL1 (← readReg MDSCR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MDSELR_EL1_SysRegRead_793ed69a5a9eaab3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EBWE ← (( do (pure (_get_MDCR_EL3_Type_EBWE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nMDSELR_EL1 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nMDSELR_EL1 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EBWE == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nMDSELR_EL1 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_EBWE == 0#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                  then
                                    (do
                                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else (X_set t 64 (__get_MDSELR_EL1 (← readReg MDSELR_EL1))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EBWE == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EBWE == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_MDSELR_EL1 (← readReg MDSELR_EL1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MDSELR_EL1 (← readReg MDSELR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECIDR_EL2_SysRegRead_22d6791638dc141a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_MECIDR_EL2 (← readReg MECIDR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MECIDR_EL2 (← readReg MECIDR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECID_A0_EL2_SysRegRead_d1ae9fcf467da39c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_MECEn ← (( do (pure (_get_SCR_EL3_Type_MECEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((! (← (IsCurrentSecurityState SS_Realm))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_MECID_A0_EL2 (← readReg MECID_A0_EL2))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MECID_A0_EL2 (← readReg MECID_A0_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECID_A1_EL2_SysRegRead_c4456c8d850c3339 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_MECEn ← (( do (pure (_get_SCR_EL3_Type_MECEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((! (← (IsCurrentSecurityState SS_Realm))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_MECID_A1_EL2 (← readReg MECID_A1_EL2))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MECID_A1_EL2 (← readReg MECID_A1_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECID_P0_EL2_SysRegRead_63d80c0de4f28c1a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_MECEn ← (( do (pure (_get_SCR_EL3_Type_MECEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((! (← (IsCurrentSecurityState SS_Realm))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_MECID_P0_EL2 (← readReg MECID_P0_EL2))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MECID_P0_EL2 (← readReg MECID_P0_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECID_P1_EL2_SysRegRead_7875ab7fe28cd25b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_MECEn ← (( do (pure (_get_SCR_EL3_Type_MECEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((! (← (IsCurrentSecurityState SS_Realm))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_MECID_P1_EL2 (← readReg MECID_P1_EL2))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MECID_P1_EL2 (← readReg MECID_P1_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECID_RL_A_EL3_SysRegRead_50a71cb28bab1988 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MECID_RL_A_EL3 (← readReg MECID_RL_A_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MFAR_EL3_SysRegRead_6520d659502d749b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MFAR_EL3 (← readReg MFAR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MIDR_EL1_SysRegRead_5aac357d91bc3b98 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_MIDR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_MIDR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_MIDR_EL1 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((← (EL2Enabled ())) : Bool)
              then (X_set t 64 (__get_VPIDR_EL2 (← readReg VPIDR_EL2)))
              else (X_set t 64 (__get_MIDR_EL1 (← readReg MIDR_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_MIDR_EL1 (← readReg MIDR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MIDR_EL1 (← readReg MIDR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAM0_EL1_SysRegRead_26602bb382f28735 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MPAM2_EL2_TRAPMPAM0EL1 ← (( do (pure (_get_MPAM2_EL2_Type_TRAPMPAM0EL1 (← readReg MPAM2_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
          then
            (do
              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__MPAM2_EL2_TRAPMPAM0EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_MPAM0_EL1 (← readReg MPAM0_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (__get_MPAM0_EL1 (← readReg MPAM0_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MPAM0_EL1 (← readReg MPAM0_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAM1_EL1_SysRegRead_85039c69dab4c388 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x900#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_MPAM1_EL1 (← (MPAM1_EL1_read ())))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_MPAM1_EL1 (← (MPAM1_EL1_read ()))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAM2_EL2_SysRegRead_8458d45c0c29ff85 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MPAM2_EL2_TRAPMPAM1EL1 ← (( do (pure (_get_MPAM2_EL2_Type_TRAPMPAM1EL1 (← readReg MPAM2_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
          then
            (do
              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__MPAM2_EL2_TRAPMPAM1EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x900#12))))
                  else (X_set t 64 (__get_MPAM1_EL1 (← (MPAM1_EL1_read ())))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (X_set t 64 (__get_MPAM2_EL2 (← readReg MPAM2_EL2)))
                  else (X_set t 64 (__get_MPAM1_EL1 (← (MPAM1_EL1_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MPAM1_EL1 (← (MPAM1_EL1_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAM2_EL2_SysRegRead_f89d395320b0f023 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (__get_MPAM2_EL2 (← readReg MPAM2_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MPAM2_EL2 (← readReg MPAM2_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAM3_EL3_SysRegRead_2770962b9f8f46c1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MPAM3_EL3 (← (MPAM3_EL3_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMHCR_EL2_SysRegRead_29e51a9bb9c934dc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x930#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (__get_MPAMHCR_EL2 (← readReg MPAMHCR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MPAMHCR_EL2 (← readReg MPAMHCR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMIDR_EL1_SysRegRead_e782b807b20cd739 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MPAMIDR_EL1_HAS_HCR ← (( do (pure (_get_MPAMIDR_EL1_Type_HAS_HCR (← readReg MPAMIDR_EL1))) ) : SailM (BitVec 1) )
  let __MPAMHCR_EL2_TRAP_MPAMIDR_EL1 ← (( do (pure (_get_MPAMHCR_EL2_Type_TRAP_MPAMIDR_EL1 (← readReg MPAMHCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAMIDR_EL1_HAS_TIDR ← (( do (pure (_get_MPAMIDR_EL1_Type_HAS_TIDR (← readReg MPAMIDR_EL1))) ) : SailM (BitVec 1) )
  let __MPAM2_EL2_TIDR ← (( do (pure (_get_MPAM2_EL2_Type_TIDR (← readReg MPAM2_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
          then
            (do
              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
          else
            (do
              if ((((← (EL2Enabled ())) && (__MPAMIDR_EL1_HAS_HCR == 1#1)) && (__MPAMHCR_EL2_TRAP_MPAMIDR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((← (EL2Enabled ())) && (__MPAMIDR_EL1_HAS_TIDR == 1#1)) && (__MPAM2_EL2_TIDR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (← (__get_MPAMIDR_EL1 (← readReg MPAMIDR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (← (__get_MPAMIDR_EL1 (← readReg MPAMIDR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (__get_MPAMIDR_EL1 (← readReg MPAMIDR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMSM_EL1_SysRegRead_8b218aacc540b1cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MPAM2_EL2_EnMPAMSM ← (( do (pure (_get_MPAM2_EL2_Type_EnMPAMSM (← readReg MPAM2_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
          then
            (do
              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__MPAM2_EL2_EnMPAMSM == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_MPAMSM_EL1 (← readReg MPAMSM_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (__get_MPAMSM_EL1 (← readReg MPAMSM_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MPAMSM_EL1 (← readReg MPAMSM_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMVPM0_EL2_SysRegRead_0960f12de90321b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x940#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (← readReg MPAMVPM0_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MPAMVPM0_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMVPM1_EL2_SysRegRead_d5133d205dd80497 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x948#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (← readReg MPAMVPM1_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MPAMVPM1_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMVPM2_EL2_SysRegRead_cd39f13f6feef099 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x950#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (← readReg MPAMVPM2_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MPAMVPM2_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMVPM3_EL2_SysRegRead_3655c8ba5ed54616 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x958#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (← readReg MPAMVPM3_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MPAMVPM3_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMVPM4_EL2_SysRegRead_2c47261ee8f811ec (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x960#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (← readReg MPAMVPM4_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MPAMVPM4_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMVPM5_EL2_SysRegRead_b3b860d951143744 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x968#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (← readReg MPAMVPM5_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MPAMVPM5_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMVPM6_EL2_SysRegRead_a456f2178fffbd2a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x970#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (← readReg MPAMVPM6_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MPAMVPM6_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMVPM7_EL2_SysRegRead_7f9fcda98e26326e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x978#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (← readReg MPAMVPM7_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MPAMVPM7_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAMVPMV_EL2_SysRegRead_3717c7fd58152b67 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MPAM3_EL3_TRAPLOWER ← (( do (pure (_get_MPAM3_EL3_Type_TRAPLOWER (← (MPAM3_EL3_read ())))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x938#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else (X_set t 64 (__get_MPAMVPMV_EL2 (← readReg MPAMVPMV_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MPAMVPMV_EL2 (← readReg MPAMVPMV_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MVFR0_EL1_SysRegRead_dd15ac4d4e4917f3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg MVFR0_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg MVFR0_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MVFR0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MVFR1_EL1_SysRegRead_ac66b9abd61faeb2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg MVFR1_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg MVFR1_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MVFR1_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MVFR2_EL1_SysRegRead_56cfaa06768c8d8a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID3 ← (( do (pure (_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID3 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg MVFR2_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg MVFR2_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg MVFR2_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def NZCV_SysRegRead_66dd3f91dc048279 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (X_set t 64 (((Zeros (n := 32)) +++ ((← readReg PSTATE).N +++ ((← readReg PSTATE).Z +++ ((← readReg PSTATE).C +++ (← readReg PSTATE).V)))) +++ (Zeros (n := 28))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (((Zeros (n := 32)) +++ ((← readReg PSTATE).N +++ ((← readReg PSTATE).Z +++ ((← readReg PSTATE).C +++ (← readReg PSTATE).V)))) +++ (Zeros (n := 28))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (((Zeros (n := 32)) +++ ((← readReg PSTATE).N +++ ((← readReg PSTATE).Z +++ ((← readReg PSTATE).C +++ (← readReg PSTATE).V)))) +++ (Zeros (n := 28))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (((Zeros (n := 32)) +++ ((← readReg PSTATE).N +++ ((← readReg PSTATE).Z +++ ((← readReg PSTATE).C +++ (← readReg PSTATE).V)))) +++ (Zeros (n := 28))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def OSDLR_EL1_SysRegRead_b4a733586ba54671 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HDFGRTR_EL2_OSDLR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_OSDLR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDOSA ← (( do (pure (_get_MDCR_EL2_Type_TDOSA (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3)) == 1#1))) <&&> (do
               (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                 (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA"))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (IsFeatureImplemented FEAT_FGT)) <&&> (do
                     (pure (! (HaveEL EL3))) <||> (do
                       (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                     (IsFeatureImplemented FEAT_DoubleLock)))) && (__HDFGRTR_EL2_OSDLR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDOSA (← readReg MDCR_EL2))) != 0b00#2))) <&&> (do
                       (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                         (__IMPDEF_boolean "Trapped by MDCR_EL2.TDOSA"))))) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (pure ((_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3)) == 1#1))) <&&> (do
                           (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                             (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA"))))) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (__get_OSDLR_EL1 (← readReg OSDLR_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3)) == 1#1))) <&&> (do
                   (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                     (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA"))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (pure ((_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3)) == 1#1))) <&&> (do
                       (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                         (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA"))))) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← (__get_OSDLR_EL1 (← readReg OSDLR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (__get_OSDLR_EL1 (← readReg OSDLR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def OSDTRRX_EL1_SysRegRead_ed7388c985c3d430 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((Halted ()) <&&> (do
           (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
      then (X_set t 64 (__get_OSDTRRX_EL1 (← readReg OSDTRRX_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                  then
                                    (do
                                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else (X_set t 64 (__get_OSDTRRX_EL1 (← readReg OSDTRRX_EL1)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else (X_set t 64 (__get_OSDTRRX_EL1 (← readReg OSDTRRX_EL1)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_OSDTRRX_EL1 (← readReg OSDTRRX_EL1)))
                  else (pure ())))))


