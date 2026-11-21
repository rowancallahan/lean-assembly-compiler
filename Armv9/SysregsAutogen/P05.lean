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
def DBGBCR_EL1_SysRegWrite_61c83a14b45e16e7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (11 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 11 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 11 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 11 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_6dec972069cd8973 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (0 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 0 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 0 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 0 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_744b1c8f0dd2fb3d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (3 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 3 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 3 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 3 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_88fc06956ff9a27d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (9 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 9 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 9 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 9 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_8f8afc10abdec5e5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (7 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 7 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 7 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 7 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_ded364def59ffa88 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (2 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 2 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 2 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 2 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_ff386e82c1b05d03 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (4 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 4 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 4 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 4 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_ffc42f78aa082453 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (14 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 14 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 14 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 14 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_ffdc1fc8f6c7fc45 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (12 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 12 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 12 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 12 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_01d1bc9e52696bd3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (7 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 7 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 7 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 7 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_0ffea2b5aaa11a7e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (15 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 15 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 15 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 15 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_29714f88a060e4b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (11 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 11 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 11 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 11 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_55cdacc69a298806 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (6 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 6 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 6 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 6 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_5c1b36bf1cfddcd3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (3 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 3 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 3 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 3 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_852dfd64d8177f24 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (8 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 8 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 8 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 8 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_937d9c663e9c5fac (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (9 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 9 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 9 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 9 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_b07af68aa09a25a4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (14 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 14 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 14 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 14 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_b6b7620b2590b0ed (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (13 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 13 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 13 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 13 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_bdc011d5eec3120d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (5 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 5 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 5 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 5 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_bfd9ab96b75f8397 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (2 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 2 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 2 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 2 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_d66d369f6bf3258b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (12 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 12 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 12 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 12 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_d9115397654925c1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (1 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 1 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 1 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 1 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_de9cae5804e73d5d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (10 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 10 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 10 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 10 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_fd95b8925256c672 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (0 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 0 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 0 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 0 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegWrite_ff943c25599ed8a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (4 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 4 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 4 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) 4 (Mk_DBGBVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGCLAIMCLR_EL1_SysRegWrite_9e17f03f8d2d5748 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGCLAIM ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGCLAIM (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGCLAIM == 1#1)) : Bool)
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
                      else writeReg DBGCLAIMCLR_EL1 (Mk_DBGCLAIMCLR_EL1_Type (← (X_read t 64)))))))
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
                  else writeReg DBGCLAIMCLR_EL1 (Mk_DBGCLAIMCLR_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg DBGCLAIMCLR_EL1 (Mk_DBGCLAIMCLR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGCLAIMSET_EL1_SysRegWrite_ebe44f0b96496255 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGCLAIM ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGCLAIM (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGCLAIM == 1#1)) : Bool)
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
                      else writeReg DBGCLAIMSET_EL1 (Mk_DBGCLAIMSET_EL1_Type (← (X_read t 64)))))))
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
                  else writeReg DBGCLAIMSET_EL1 (Mk_DBGCLAIMSET_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg DBGCLAIMSET_EL1 (Mk_DBGCLAIMSET_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGDTRTX_EL0_SysRegWrite_b44ad1253b524254 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  if ((← (Halted ())) : Bool)
  then writeReg DBGDTRTX_EL0 (← (X_read t 64))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
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
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                          else writeReg DBGDTRTX_EL0 (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
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
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                          else writeReg DBGDTRTX_EL0 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else writeReg DBGDTRTX_EL0 (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg DBGDTRTX_EL0 (← (X_read t 64))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGDTR_EL0_SysRegWrite_a660c15660434176 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  if ((← (Halted ())) : Bool)
  then (DBGDTR_EL0_write (Mk_DBGDTR_EL0_Type (← (X_read t 64))))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
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
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                          else (DBGDTR_EL0_write (Mk_DBGDTR_EL0_Type (← (X_read t 64)))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
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
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                          else (DBGDTR_EL0_write (Mk_DBGDTR_EL0_Type (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else (DBGDTR_EL0_write (Mk_DBGDTR_EL0_Type (← (X_read t 64))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (DBGDTR_EL0_write (Mk_DBGDTR_EL0_Type (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGPRCR_EL1_SysRegWrite_61b4445159bc717f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDOSA ← (( do (pure (_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGPRCR_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGPRCR_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGPRCR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDOSA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg DBGPRCR_EL1 (Mk_DBGPRCR_EL1_Type (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg DBGPRCR_EL1 (Mk_DBGPRCR_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg DBGPRCR_EL1 (Mk_DBGPRCR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGVCR32_EL2_SysRegWrite_2027ba18d0bb0f7c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else writeReg DBGVCR32_EL2 (Mk_DBGVCR32_EL2_Type (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg DBGVCR32_EL2 (Mk_DBGVCR32_EL2_Type (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_0d601db72f451078 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 15 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 15 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 15 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_18462f760618e8fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 7 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 7 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 7 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_1c79cf637de59bc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 0 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 0 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 0 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_26c799c330f26506 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 9 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 9 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 9 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_2c96fce13ad4bca3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 5 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 5 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 5 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_3550aa3a97d9acb5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 14 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 14 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 14 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_3d5a9e41f298edee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 3 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 3 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 3 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_3fb61300ed3d0b2e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 12 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 12 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 12 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_5874322f7df6e594 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 2 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 2 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 2 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_6b9bd001fa5472bf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 4 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 4 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 4 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_8596ad7b1510b4d0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 10 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 10 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 10 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_99531412fe248a70 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 11 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 11 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 11 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_9a01e4eef27687e1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 6 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 6 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 6 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_b844eaa7818871c4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 13 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 13 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 13 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_bbc38f4d76601b93 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 8 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 8 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 8 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_EL1_SysRegWrite_f25a750222e0315f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWCRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 1 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 1 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) 1 (Mk_DBGWCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_0e74b22895679043 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 9 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 9 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 9 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_11bcd12fdb930549 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 6 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 6 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 6 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_1e44505a2360dca7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 7 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 7 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 7 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_1fb1fea2e690a0e3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 0 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 0 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 0 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_23079da74592c125 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 4 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 4 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 4 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_4c12a1266354ed31 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 3 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 3 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 3 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_5c185ce0c31c928c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 14 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 14 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 14 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_7c615d5af77d3ffb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 10 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 10 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 10 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_91254f0a6285bce0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 12 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 12 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 12 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_9a9c86f74847526f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 8 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 8 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 8 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_b09d023fdf3ab695 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 1 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 1 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 1 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_c2a564a92621de17 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 11 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 11 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 11 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_c31d1fb9ddb2a17a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 2 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 2 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 2 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_e3e0a8c119a9f320 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 13 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 13 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 13 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_f3a1e531b8f544ee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 15 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 15 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 15 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegWrite_fdd8c8e27256c2b3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGWVRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_DBGWVRn_EL1 == 1#1)) : Bool)
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
                                  then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 5 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 5 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGWVR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) 5 (Mk_DBGWVR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DIT_SysRegWrite_cb82290c1722296d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with DIT := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 24)]))) }
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with DIT := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 24)]))) }
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with DIT := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 24)]))) }
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg PSTATE { (← readReg PSTATE) with DIT := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 24)]))) }
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DLR_EL0_SysRegWrite_7614507cf751cf9d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else writeReg DLR_EL0 (← (X_read t 64))

/-- Type quantifiers: t : Int -/
def DSPSR_EL0_SysRegWrite_2829d14e4c67df55 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type (← (X_read t 64)))

/-- Type quantifiers: t : Int -/
def ELR_EL1_SysRegWrite_68df116f8fbbefed (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x230#12) (← (X_read t 64)))
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
              then writeReg ELR_EL1 (← (X_read t 64))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg ELR_EL1 (← (X_read t 64))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ELR_EL2_SysRegWrite_428ab6f83a3c959c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((IsFeatureImplemented FEAT_GCS) <&&> (do
                 (GetCurrentEXLOCKEN ())) <&&> (do
                 (pure (! (← (Halted ()))))) <&&> (do
                 (pure ((← readReg PSTATE).EXLOCK == 1#1))) <&&> (do
                 (EL2Enabled ())))) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (EXLOCKException ())
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then writeReg ELR_EL1 (← (X_read t 64))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((IsFeatureImplemented FEAT_GCS) <&&> (do
                   (GetCurrentEXLOCKEN ())) <&&> (do
                   (pure (! (← (Halted ()))))) <&&> (do
                   (pure ((← readReg PSTATE).EXLOCK == 1#1))))) : Bool)
              then (EXLOCKException ())
              else writeReg ELR_EL2 (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ELR_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ELR_EL2_SysRegWrite_9fa5a0aa6e6a37d8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((IsFeatureImplemented FEAT_GCS) <&&> (do
               (GetCurrentEXLOCKEN ())) <&&> (do
               (pure (! (← (Halted ()))))) <&&> (do
               (pure ((← readReg PSTATE).EXLOCK == 1#1))) <&&> (do
               (pure ((_get_HCR_EL2_Type_NV (← readReg HCR_EL2)) == 0#1)) <||> (do
                 (EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b01#2))))))) : Bool)
          then (EXLOCKException ())
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b011#3))))) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x230#12) (← (X_read t 64)))
                  else writeReg ELR_EL1 (← (X_read t 64)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((IsFeatureImplemented FEAT_GCS) <&&> (do
                     (GetCurrentEXLOCKEN ())) <&&> (do
                     (pure (! (← (Halted ()))))) <&&> (do
                     (pure ((← readReg PSTATE).EXLOCK == 1#1))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
              then (EXLOCKException ())
              else
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then writeReg ELR_EL2 (← (X_read t 64))
                  else writeReg ELR_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ELR_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ELR_EL3_SysRegWrite_95989f8c3fc9cabc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_EXLOCK ← (( do (pure (← readReg PSTATE).EXLOCK) ) : SailM (BitVec 1) )
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
                  if (((←((IsFeatureImplemented FEAT_GCS) <&&> (do
                         (GetCurrentEXLOCKEN ())) <&&> (do
                         (pure (! (← (Halted ()))))))) && (__PSTATE_EXLOCK == 1#1)) : Bool)
                  then (EXLOCKException ())
                  else writeReg ELR_EL3 (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERRSELR_EL1_SysRegWrite_91762c9f88299554 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TWERR ← (( do (pure (_get_SCR_EL3_Type_TWERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ERRSELR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ERRSELR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ERRSELR_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg ERRSELR_EL1 (Mk_ERRSELR_EL1_Type (← (X_read t 64)))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ERRSELR_EL1 (Mk_ERRSELR_EL1_Type (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ERRSELR_EL1 (Mk_ERRSELR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXADDR_EL1_SysRegWrite_279c161c3f15ad75 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TWERR ← (( do (pure (_get_SCR_EL3_Type_TWERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ERXADDR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ERXADDR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ERXADDR_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg ERXADDR_EL1 (← (X_read t 64))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ERXADDR_EL1 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ERXADDR_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXCTLR_EL1_SysRegWrite_906c95adeb6439bf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TWERR ← (( do (pure (_get_SCR_EL3_Type_TWERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ERXCTLR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ERXCTLR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ERXCTLR_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg ERXCTLR_EL1 (← (X_read t 64))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ERXCTLR_EL1 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ERXCTLR_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC0_EL1_SysRegWrite_58590d278dd5aa2a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TWERR ← (( do (pure (_get_SCR_EL3_Type_TWERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ERXMISCn_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ERXMISCn_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ERXMISCn_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg ERXMISC0_EL1 (← (X_read t 64))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ERXMISC0_EL1 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ERXMISC0_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC1_EL1_SysRegWrite_93405d7656da2145 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TWERR ← (( do (pure (_get_SCR_EL3_Type_TWERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ERXMISCn_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ERXMISCn_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ERXMISCn_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg ERXMISC1_EL1 (← (X_read t 64))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ERXMISC1_EL1 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ERXMISC1_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC2_EL1_SysRegWrite_f9de127bf1e8564c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TWERR ← (( do (pure (_get_SCR_EL3_Type_TWERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ERXMISCn_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ERXMISCn_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ERXMISCn_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg ERXMISC2_EL1 (← (X_read t 64))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ERXMISC2_EL1 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ERXMISC2_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC3_EL1_SysRegWrite_cdfbf138332e928b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TWERR ← (( do (pure (_get_SCR_EL3_Type_TWERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ERXMISCn_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ERXMISCn_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ERXMISCn_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg ERXMISC3_EL1 (← (X_read t 64))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ERXMISC3_EL1 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ERXMISC3_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXPFGCDN_EL1_SysRegWrite_0c8c2a0a68bbf725 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIEN ← (( do (pure (_get_SCR_EL3_Type_FIEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FIEN ← (( do (pure (_get_HCR_EL2_Type_FIEN (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ERXPFGCDN_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ERXPFGCDN_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ERXPFGCDN_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIEN == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg ERXPFGCDN_EL1 (← (X_read t 64))))))
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
                  else writeReg ERXPFGCDN_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ERXPFGCDN_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXPFGCTL_EL1_SysRegWrite_19ab79f4cbeee79c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIEN ← (( do (pure (_get_SCR_EL3_Type_FIEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FIEN ← (( do (pure (_get_HCR_EL2_Type_FIEN (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ERXPFGCTL_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ERXPFGCTL_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ERXPFGCTL_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIEN == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg ERXPFGCTL_EL1 (← (X_read t 64))))))
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
                  else writeReg ERXPFGCTL_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ERXPFGCTL_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXSTATUS_EL1_SysRegWrite_1a78a129cb7959a2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TWERR ← (( do (pure (_get_SCR_EL3_Type_TWERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ERXSTATUS_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ERXSTATUS_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TERR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ERXSTATUS_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg ERXSTATUS_EL1 (← (X_read t 64))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TWERR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ERXSTATUS_EL1 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ERXSTATUS_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ESR_EL1_SysRegWrite_2d18d2815288c81b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ESR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ESR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TVM == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ESR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x138#12) (← (X_read t 64)))
                  else writeReg ESR_EL1 (Mk_ESR_EL1_Type (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg ESR_EL2 (Mk_ESR_EL2_Type (← (X_read t 64)))
              else writeReg ESR_EL1 (Mk_ESR_EL1_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ESR_EL1 (Mk_ESR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ESR_EL1_SysRegWrite_2e8be6fdfdb29f96 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg ESR_EL1 (Mk_ESR_EL1_Type (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg ESR_EL2 (Mk_ESR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ESR_EL2 (Mk_ESR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ESR_EL1_SysRegWrite_c81bcd0055a15f7e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x138#12) (← (X_read t 64)))
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
              then writeReg ESR_EL1 (Mk_ESR_EL1_Type (← (X_read t 64)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg ESR_EL1 (Mk_ESR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ESR_EL3_SysRegWrite_d8e4dd481971160d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg ESR_EL3 (Mk_ESR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FAR_EL1_SysRegWrite_6ebf0555a014e9a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x220#12) (← (X_read t 64)))
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
              then writeReg FAR_EL1 (← (X_read t 64))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg FAR_EL1 (← (X_read t 64))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FAR_EL2_SysRegWrite_238df3b108707325 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_FAR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_FAR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TVM == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_FAR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x220#12) (← (X_read t 64)))
                  else writeReg FAR_EL1 (← (X_read t 64)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg FAR_EL2 (← (X_read t 64))
              else writeReg FAR_EL1 (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg FAR_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FAR_EL2_SysRegWrite_81edbabe253f2359 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg FAR_EL1 (← (X_read t 64))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg FAR_EL2 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg FAR_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FAR_EL3_SysRegWrite_d150ecea5bb2beb8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg FAR_EL3 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FPCR_SysRegWrite_b4b7f4f4f63e39e4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          else (__set_FPCR (Mk_FPCR_Type (← (X_read t 64))))))))))
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
                          else (__set_FPCR (Mk_FPCR_Type (← (X_read t 64)))))))))
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
                          else (__set_FPCR (Mk_FPCR_Type (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_TFP == 1#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))
                  else (__set_FPCR (Mk_FPCR_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FPEXC32_EL2_SysRegWrite_5a68dce0d934d834 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              else (__set_FPEXC32_EL2 (Mk_FPEXC32_EL2_Type (← (X_read t 64))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((__CPTR_EL3_TFP == 1#1) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))
                      else (__set_FPEXC32_EL2 (Mk_FPEXC32_EL2_Type (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def FPSR_SysRegWrite_d0a803d1b7d0c76d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          else writeReg FPSR (Mk_FPSR_Type (← (X_read t 64)))))))))
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
                          else writeReg FPSR (Mk_FPSR_Type (← (X_read t 64))))))))
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
                          else writeReg FPSR (Mk_FPSR_Type (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_TFP == 1#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))
                  else writeReg FPSR (Mk_FPSR_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCR_EL1_SysRegWrite_f456e3e42b53d94b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg GCR_EL1 (Mk_GCR_EL1_Type (← (X_read t 64))))))
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
                  else writeReg GCR_EL1 (Mk_GCR_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg GCR_EL1 (Mk_GCR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSCRE0_EL1_SysRegWrite_23a06c4b91079e78 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nGCS_EL0 ← (( do (pure (_get_HFGWTR_EL2_Type_nGCS_EL0 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nGCS_EL0 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg GCSCRE0_EL1 (Mk_GCSCRE0_EL1_Type (← (X_read t 64))))))
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
                  else writeReg GCSCRE0_EL1 (Mk_GCSCRE0_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg GCSCRE0_EL1 (Mk_GCSCRE0_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSCR_EL1_SysRegWrite_59dd068f82662ce4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nGCS_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_nGCS_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nGCS_EL1 == 0#1)) : Bool)
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
                      then (NVMem_set (BitVec.toNat 0x8D0#12) (← (X_read t 64)))
                      else writeReg GCSCR_EL1 (Mk_GCSCR_EL1_Type (← (X_read t 64)))))))
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
                      then writeReg GCSCR_EL2 (Mk_GCSCR_EL2_Type (← (X_read t 64)))
                      else writeReg GCSCR_EL1 (Mk_GCSCR_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg GCSCR_EL1 (Mk_GCSCR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSCR_EL1_SysRegWrite_f74f83dd6c534093 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x8D0#12) (← (X_read t 64)))
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
                      else writeReg GCSCR_EL1 (Mk_GCSCR_EL1_Type (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg GCSCR_EL1 (Mk_GCSCR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSCR_EL2_SysRegWrite_69ee046b6f0cd4a2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg GCSCR_EL2 (Mk_GCSCR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg GCSCR_EL2 (Mk_GCSCR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSCR_EL3_SysRegWrite_7d39fd6ab827245b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg GCSCR_EL3 (Mk_GCSCR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPR_EL0_SysRegWrite_5641ca6b298c3087 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nGCS_EL0 ← (( do (pure (_get_HFGWTR_EL2_Type_nGCS_EL0 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nGCS_EL0 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_GCSEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg GCSPR_EL0 (Mk_GCSPR_EL0_Type (← (X_read t 64))))))
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
                  else writeReg GCSPR_EL0 (Mk_GCSPR_EL0_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg GCSPR_EL0 (Mk_GCSPR_EL0_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPR_EL1_SysRegWrite_12e427956c7e46df (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x8C0#12) (← (X_read t 64)))
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
                      else writeReg GCSPR_EL1 (Mk_GCSPR_EL1_Type (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg GCSPR_EL1 (Mk_GCSPR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPR_EL1_SysRegWrite_f94f037e4dc25b54 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_GCSEn ← (( do (pure (_get_SCR_EL3_Type_GCSEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nGCS_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_nGCS_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nGCS_EL1 == 0#1)) : Bool)
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
                      then (NVMem_set (BitVec.toNat 0x8C0#12) (← (X_read t 64)))
                      else writeReg GCSPR_EL1 (Mk_GCSPR_EL1_Type (← (X_read t 64)))))))
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
                      then writeReg GCSPR_EL2 (Mk_GCSPR_EL2_Type (← (X_read t 64)))
                      else writeReg GCSPR_EL1 (Mk_GCSPR_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg GCSPR_EL1 (Mk_GCSPR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPR_EL2_SysRegWrite_f0fb2104021e0393 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg GCSPR_EL2 (Mk_GCSPR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg GCSPR_EL2 (Mk_GCSPR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPR_EL3_SysRegWrite_2c3789955c87eb01 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg GCSPR_EL3 (Mk_GCSPR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GPCCR_EL3_SysRegWrite_34a621e690dc851f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (__set_GPCCR_EL3 (Mk_GPCCR_EL3_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GPTBR_EL3_SysRegWrite_6f7a8066a1cb6176 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg GPTBR_EL3 (Mk_GPTBR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HACR_EL2_SysRegWrite_a6347b2f3c503b39 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg HACR_EL2 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HACR_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HAFGRTR_EL2_SysRegWrite_9a7efd61edbaec8c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1E8#12) (← (X_read t 64)))
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
                  else writeReg HAFGRTR_EL2 (Mk_HAFGRTR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HAFGRTR_EL2 (Mk_HAFGRTR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HCRX_EL2_SysRegWrite_e32bbb7de8dc8ae3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0xA0#8) (← (X_read t 64)))
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
                  else writeReg HCRX_EL2 (Mk_HCRX_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HCRX_EL2 (Mk_HCRX_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HCR_EL2_SysRegWrite_f7613e1ff35a2f03 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x078#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg HCR_EL2 (Mk_HCR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HCR_EL2 (Mk_HCR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HDFGRTR2_EL2_SysRegWrite_43901f5d0ed8f1ff (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1A0#12) (← (X_read t 64)))
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
                  else writeReg HDFGRTR2_EL2 (Mk_HDFGRTR2_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HDFGRTR2_EL2 (Mk_HDFGRTR2_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HDFGRTR_EL2_SysRegWrite_3a295a56b6f65626 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1D0#12) (← (X_read t 64)))
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
                  else writeReg HDFGRTR_EL2 (Mk_HDFGRTR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HDFGRTR_EL2 (Mk_HDFGRTR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HDFGWTR2_EL2_SysRegWrite_e3193a6400b6a613 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1B0#12) (← (X_read t 64)))
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
                  else writeReg HDFGWTR2_EL2 (Mk_HDFGWTR2_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HDFGWTR2_EL2 (Mk_HDFGWTR2_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HDFGWTR_EL2_SysRegWrite_5484cb7bd2cd2662 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1D8#12) (← (X_read t 64)))
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
                  else writeReg HDFGWTR_EL2 (Mk_HDFGWTR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HDFGWTR_EL2 (Mk_HDFGWTR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGITR2_EL2_SysRegWrite_41576daf42281ba5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x310#12) (← (X_read t 64)))
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
                  else writeReg HFGITR2_EL2 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HFGITR2_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGITR_EL2_SysRegWrite_11b3edecdb0dbac6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1C8#12) (← (X_read t 64)))
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
                  else writeReg HFGITR_EL2 (Mk_HFGITR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HFGITR_EL2 (Mk_HFGITR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGRTR2_EL2_SysRegWrite_31d517272a11cc63 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x2C0#12) (← (X_read t 64)))
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
                  else writeReg HFGRTR2_EL2 (Mk_HFGRTR2_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HFGRTR2_EL2 (Mk_HFGRTR2_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGRTR_EL2_SysRegWrite_fa73b98f16c9efee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1B8#12) (← (X_read t 64)))
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
                  else writeReg HFGRTR_EL2 (Mk_HFGRTR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HFGRTR_EL2 (Mk_HFGRTR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGWTR2_EL2_SysRegWrite_9115a08ec76ef20a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x2C8#12) (← (X_read t 64)))
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
                  else writeReg HFGWTR2_EL2 (Mk_HFGWTR2_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HFGWTR2_EL2 (Mk_HFGWTR2_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HFGWTR_EL2_SysRegWrite_f913499e5a0813f2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1C0#12) (← (X_read t 64)))
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
                  else writeReg HFGWTR_EL2 (Mk_HFGWTR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HFGWTR_EL2 (Mk_HFGWTR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HPFAR_EL2_SysRegWrite_cc86ce0a0fcde19a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg HPFAR_EL2 (Mk_HPFAR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HPFAR_EL2 (Mk_HPFAR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HSTR_EL2_SysRegWrite_bdeca187ad74c419 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x080#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg HSTR_EL2 (Mk_HSTR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg HSTR_EL2 (Mk_HSTR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_AP0R_EL1_SysRegWrite_1d272226dc8d2255 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICC_AP0R_EL1_SysRegWrite_2e8737fdf3d4b8b5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICC_AP0R_EL1_SysRegWrite_7622c42003c1547b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then writeReg ICV_AP0R_EL1 (vectorUpdate (← readReg ICV_AP0R_EL1) 0 (← (X_read t 64)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ICC_AP0R_EL1 (vectorUpdate (← readReg ICC_AP0R_EL1) 0 (← (X_read t 64))))))))
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
                      else writeReg ICC_AP0R_EL1 (vectorUpdate (← readReg ICC_AP0R_EL1) 0 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICC_AP0R_EL1 (vectorUpdate (← readReg ICC_AP0R_EL1) 0 (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_AP0R_EL1_SysRegWrite_a8bec11c8e53045a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICC_AP1R_EL1_SysRegWrite_0d9519f401c9d3ae (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICC_AP1R_EL1_SysRegWrite_27852b8ac573cdcd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICC_AP1R_EL1_SysRegWrite_58ad13edd90bb69b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then writeReg ICV_AP1R_EL1 (vectorUpdate (← readReg ICV_AP1R_EL1) 0 (Mk_ICV_AP1R_EL1_Type (← (X_read t 64))))
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
                                  then writeReg ICC_AP1R_EL1_S (vectorUpdate (← readReg ICC_AP1R_EL1_S) 0 (Mk_ICC_AP1R_EL1_Type (← (X_read t 64))))
                                  else writeReg ICC_AP1R_EL1_NS (vectorUpdate (← readReg ICC_AP1R_EL1_NS) 0 (Mk_ICC_AP1R_EL1_Type (← (X_read t 64)))))
                              else (ICC_AP1R_EL1_set 0 (Mk_ICC_AP1R_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg ICC_AP1R_EL1_S (vectorUpdate (← readReg ICC_AP1R_EL1_S) 0 (Mk_ICC_AP1R_EL1_Type (← (X_read t 64))))
                              else writeReg ICC_AP1R_EL1_NS (vectorUpdate (← readReg ICC_AP1R_EL1_NS) 0 (Mk_ICC_AP1R_EL1_Type (← (X_read t 64)))))
                          else (ICC_AP1R_EL1_set 0 (Mk_ICC_AP1R_EL1_Type (← (X_read t 64))))))))
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
                      then writeReg ICC_AP1R_EL1_S (vectorUpdate (← readReg ICC_AP1R_EL1_S) 0 (Mk_ICC_AP1R_EL1_Type (← (X_read t 64))))
                      else writeReg ICC_AP1R_EL1_NS (vectorUpdate (← readReg ICC_AP1R_EL1_NS) 0 (Mk_ICC_AP1R_EL1_Type (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_AP1R_EL1_SysRegWrite_a8824fb00a7f4207 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICC_ASGI1R_EL1_SysRegWrite_588d10b57224783c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
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
                              else writeReg ICC_ASGI1R_EL1 (Mk_ICC_ASGI1R_EL1_Type (← (X_read t 64)))))))))
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
                      else writeReg ICC_ASGI1R_EL1 (Mk_ICC_ASGI1R_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICC_ASGI1R_EL1 (Mk_ICC_ASGI1R_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_BPR0_EL1_SysRegWrite_4ea118667d9d50cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then writeReg ICV_BPR0_EL1 (Mk_ICV_BPR0_EL1_Type (← (X_read t 64)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ICC_BPR0_EL1 (Mk_ICC_BPR0_EL1_Type (← (X_read t 64))))))))
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
                      else writeReg ICC_BPR0_EL1 (Mk_ICC_BPR0_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICC_BPR0_EL1 (Mk_ICC_BPR0_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_CTLR_EL1_SysRegWrite_6b2222909cfe4181 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then writeReg ICV_CTLR_EL1 (Mk_ICV_CTLR_EL1_Type (← (X_read t 64)))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                          then writeReg ICV_CTLR_EL1 (Mk_ICV_CTLR_EL1_Type (← (X_read t 64)))
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
                                      then writeReg ICC_CTLR_EL1_S (Mk_ICC_CTLR_EL1_Type (← (X_read t 64)))
                                      else writeReg ICC_CTLR_EL1_NS (Mk_ICC_CTLR_EL1_Type (← (X_read t 64))))
                                  else (ICC_CTLR_EL1_write (Mk_ICC_CTLR_EL1_Type (← (X_read t 64)))))))))))
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
                              then writeReg ICC_CTLR_EL1_S (Mk_ICC_CTLR_EL1_Type (← (X_read t 64)))
                              else writeReg ICC_CTLR_EL1_NS (Mk_ICC_CTLR_EL1_Type (← (X_read t 64))))
                          else (ICC_CTLR_EL1_write (Mk_ICC_CTLR_EL1_Type (← (X_read t 64))))))))
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
                      then writeReg ICC_CTLR_EL1_S (Mk_ICC_CTLR_EL1_Type (← (X_read t 64)))
                      else writeReg ICC_CTLR_EL1_NS (Mk_ICC_CTLR_EL1_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_CTLR_EL3_SysRegWrite_032d9412ecb7b900 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg ICC_CTLR_EL3 (Mk_ICC_CTLR_EL3_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_DIR_EL1_SysRegWrite_956e5112d301f88c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TDIR ← (( do (pure (_get_ICH_HCR_EL2_Type_TDIR (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
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
                  if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TDIR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TC == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_FMO == 1#1)) : Bool)
                          then writeReg ICV_DIR_EL1 (Mk_ICV_DIR_EL1_Type (← (X_read t 64)))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                              then writeReg ICV_DIR_EL1 (Mk_ICV_DIR_EL1_Type (← (X_read t 64)))
                              else
                                (do
                                  if ((←((pure (HaveEL EL3)) <&&> (do
                                       (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                                  then
                                    (do
                                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else writeReg ICC_DIR_EL1 (Mk_ICC_DIR_EL1_Type (← (X_read t 64))))))))))
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
                      else writeReg ICC_DIR_EL1 (Mk_ICC_DIR_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICC_DIR_EL1 (Mk_ICC_DIR_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_IGRPEN0_EL1_SysRegWrite_dcea5bb07e468846 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ICC_IGRPENn_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ICC_IGRPENn_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ICC_IGRPENn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_FMO == 1#1)) : Bool)
                          then writeReg ICV_IGRPEN0_EL1 (Mk_ICV_IGRPEN0_EL1_Type (← (X_read t 64)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg ICC_IGRPEN0_EL1 (Mk_ICC_IGRPEN0_EL1_Type (← (X_read t 64)))))))))
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
                      else writeReg ICC_IGRPEN0_EL1 (Mk_ICC_IGRPEN0_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICC_IGRPEN0_EL1 (Mk_ICC_IGRPEN0_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_IGRPEN1_EL1_SysRegWrite_a249f92f5cac95a3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL1_SRE ← (( do (pure (_get_ICC_SRE_EL1_Type_SRE (← (ICC_SRE_EL1_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_ICC_IGRPENn_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_ICC_IGRPENn_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_ICC_IGRPENn_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                          then writeReg ICV_IGRPEN1_EL1 (Mk_ICV_IGRPEN1_EL1_Type (← (X_read t 64)))
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
                                      then writeReg ICC_IGRPEN1_EL1_S (Mk_ICC_IGRPEN1_EL1_Type (← (X_read t 64)))
                                      else writeReg ICC_IGRPEN1_EL1_NS (Mk_ICC_IGRPEN1_EL1_Type (← (X_read t 64))))
                                  else (ICC_IGRPEN1_EL1_write (Mk_ICC_IGRPEN1_EL1_Type (← (X_read t 64)))))))))))
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
                              then writeReg ICC_IGRPEN1_EL1_S (Mk_ICC_IGRPEN1_EL1_Type (← (X_read t 64)))
                              else writeReg ICC_IGRPEN1_EL1_NS (Mk_ICC_IGRPEN1_EL1_Type (← (X_read t 64))))
                          else (ICC_IGRPEN1_EL1_write (Mk_ICC_IGRPEN1_EL1_Type (← (X_read t 64))))))))
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
                      then writeReg ICC_IGRPEN1_EL1_S (Mk_ICC_IGRPEN1_EL1_Type (← (X_read t 64)))
                      else writeReg ICC_IGRPEN1_EL1_NS (Mk_ICC_IGRPEN1_EL1_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_IGRPEN1_EL3_SysRegWrite_b957139b0969fa79 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg ICC_IGRPEN1_EL3 (Mk_ICC_IGRPEN1_EL3_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_PMR_EL1_SysRegWrite_4d3a3fb3d6e1e44e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then writeReg ICV_PMR_EL1 (Mk_ICV_PMR_EL1_Type (← (X_read t 64)))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
                          then writeReg ICV_PMR_EL1 (Mk_ICV_PMR_EL1_Type (← (X_read t 64)))
                          else
                            (do
                              if ((←((pure (HaveEL EL3)) <&&> (do
                                   (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg ICC_PMR_EL1 (Mk_ICC_PMR_EL1_Type (← (X_read t 64)))))))))
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
                      else writeReg ICC_PMR_EL1 (Mk_ICC_PMR_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICC_PMR_EL1 (Mk_ICC_PMR_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_SGI0R_EL1_SysRegWrite_97ea36eebda9c84c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
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
                              else writeReg ICC_SGI0R_EL1 (Mk_ICC_SGI0R_EL1_Type (← (X_read t 64)))))))))
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
                      else writeReg ICC_SGI0R_EL1 (Mk_ICC_SGI0R_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICC_SGI0R_EL1 (Mk_ICC_SGI0R_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_SGI1R_EL1_SysRegWrite_bd688469b6075cd1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__HCR_EL2_IMO == 1#1)) : Bool)
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
                              else writeReg ICC_SGI1R_EL1 (Mk_ICC_SGI1R_EL1_Type (← (X_read t 64)))))))))
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
                      else writeReg ICC_SGI1R_EL1 (Mk_ICC_SGI1R_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICC_SGI1R_EL1 (Mk_ICC_SGI1R_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_SRE_EL1_SysRegWrite_b4fd95205f21b2e7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          then writeReg ICC_SRE_EL1_S (Mk_ICC_SRE_EL1_Type (← (X_read t 64)))
                          else writeReg ICC_SRE_EL1_NS (Mk_ICC_SRE_EL1_Type (← (X_read t 64))))
                      else (ICC_SRE_EL1_write (Mk_ICC_SRE_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg ICC_SRE_EL1_S (Mk_ICC_SRE_EL1_Type (← (X_read t 64)))
                          else writeReg ICC_SRE_EL1_NS (Mk_ICC_SRE_EL1_Type (← (X_read t 64))))
                      else (ICC_SRE_EL1_write (Mk_ICC_SRE_EL1_Type (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then writeReg ICC_SRE_EL1_S (Mk_ICC_SRE_EL1_Type (← (X_read t 64)))
                  else writeReg ICC_SRE_EL1_NS (Mk_ICC_SRE_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_SRE_EL2_SysRegWrite_84bc0d6cdc7c9072 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg ICC_SRE_EL2 (Mk_ICC_SRE_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg ICC_SRE_EL2 (Mk_ICC_SRE_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_SRE_EL3_SysRegWrite_b650b212ede313fc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg ICC_SRE_EL3 (Mk_ICC_SRE_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_AP0R_EL2_SysRegWrite_1b21d2434fab897a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP0R_EL2_SysRegWrite_78fe7c56d4742066 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x480#12) +i (8 *i 0)) (← (X_read t 64)))
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
              else writeReg ICH_AP0R_EL2 (vectorUpdate (← readReg ICH_AP0R_EL2) 0 (Mk_ICH_AP0R_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_AP0R_EL2 (vectorUpdate (← readReg ICH_AP0R_EL2) 0 (Mk_ICH_AP0R_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_AP0R_EL2_SysRegWrite_be89bf34888417e0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP0R_EL2_SysRegWrite_ed1ffcaf90ab8639 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_EL2_SysRegWrite_20248cc458e10785 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_EL2_SysRegWrite_9327d1291a4f4958 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_EL2_SysRegWrite_b4a60e153456008a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_SRE ← (( do (pure (_get_ICC_SRE_EL2_Type_SRE (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_SRE ← (( do (pure (_get_ICC_SRE_EL3_Type_SRE (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_EL2_SysRegWrite_d831d83b4ca8a5a2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x4A0#12) +i (8 *i 0)) (← (X_read t 64)))
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
              else writeReg ICH_AP1R_EL2 (vectorUpdate (← readReg ICH_AP1R_EL2) 0 (Mk_ICH_AP1R_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_AP1R_EL2 (vectorUpdate (← readReg ICH_AP1R_EL2) 0 (Mk_ICH_AP1R_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_HCR_EL2_SysRegWrite_d09a9dfdfbf35716 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x4C0#12) (← (X_read t 64)))
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
              else writeReg ICH_HCR_EL2 (Mk_ICH_HCR_EL2_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_HCR_EL2 (Mk_ICH_HCR_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_1726583f5c5d911a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 7)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 7 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 7 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_377d2c4427bc7a74 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 11)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 11 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 11 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_3b6fa0a247977dad (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 14)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 14 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 14 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_3b8d5d6ae4931c55 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 9)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 9 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 9 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_3ca439f034b85455 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 3)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 3 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 3 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_60f29686bdc4ef5f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 4)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 4 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 4 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_7f74a03659a9be73 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 13)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 13 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 13 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_8674efc2931dff61 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 5)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 5 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 5 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_88b3b2552632aea7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 1)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 1 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 1 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_899098384db50f2b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 6)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 6 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 6 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_8e2173d5288ec9f6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 0)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 0 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 0 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_ada04edc200eb7de (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 12)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 12 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 12 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_af9b8f005bb45cf2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 15)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 15 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 15 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_ce3f5174c2a18c3b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 2)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 2 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 2 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_d4cc97ca4abc2b38 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 8)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 8 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 8 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_EL2_SysRegWrite_fd7b4774b600f5ba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set ((BitVec.toNat 0x400#12) +i (8 *i 10)) (← (X_read t 64)))
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
              else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 10 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) 10 (Mk_ICH_LR_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_VMCR_EL2_SysRegWrite_dff88313df61ad5f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x4C8#12) (← (X_read t 64)))
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
              else writeReg ICH_VMCR_EL2 (Mk_ICH_VMCR_EL2_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICH_VMCR_EL2 (Mk_ICH_VMCR_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_BPR1_EL1_SysRegWrite_cf350ee97c59e5e0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then writeReg ICV_BPR1_EL1 (Mk_ICV_BPR1_EL1_Type (← (X_read t 64)))
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
                                  then writeReg ICC_BPR1_EL1_S (Mk_ICC_BPR1_EL1_Type (← (X_read t 64)))
                                  else writeReg ICC_BPR1_EL1_NS (Mk_ICC_BPR1_EL1_Type (← (X_read t 64))))
                              else (ICC_BPR1_EL1_write (Mk_ICC_BPR1_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg ICC_BPR1_EL1_S (Mk_ICC_BPR1_EL1_Type (← (X_read t 64)))
                              else writeReg ICC_BPR1_EL1_NS (Mk_ICC_BPR1_EL1_Type (← (X_read t 64))))
                          else (ICC_BPR1_EL1_write (Mk_ICC_BPR1_EL1_Type (← (X_read t 64))))))))
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
                      then writeReg ICC_BPR1_EL1_S (Mk_ICC_BPR1_EL1_Type (← (X_read t 64)))
                      else writeReg ICC_BPR1_EL1_NS (Mk_ICC_BPR1_EL1_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_EOIR0_EL1_SysRegWrite_4d99677932f49dc7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then writeReg ICV_EOIR0_EL1 (Mk_ICV_EOIR0_EL1_Type (← (X_read t 64)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ICC_EOIR0_EL1 (Mk_ICC_EOIR0_EL1_Type (← (X_read t 64))))))))
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
                      else writeReg ICC_EOIR0_EL1 (Mk_ICC_EOIR0_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICC_EOIR0_EL1 (Mk_ICC_EOIR0_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_EOIR1_EL1_SysRegWrite_a2fbace49f2a9362 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then writeReg ICV_EOIR1_EL1 (Mk_ICV_EOIR1_EL1_Type (← (X_read t 64)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg ICC_EOIR1_EL1 (Mk_ICC_EOIR1_EL1_Type (← (X_read t 64))))))))
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
                      else writeReg ICC_EOIR1_EL1 (Mk_ICC_EOIR1_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg ICC_EOIR1_EL1 (Mk_ICC_EOIR1_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def IFSR32_EL2_SysRegWrite_a0242d47ef5c27a4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg IFSR32_EL2 (Mk_IFSR32_EL2_Type (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg IFSR32_EL2 (Mk_IFSR32_EL2_Type (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def LORC_EL1_SysRegWrite_266317162c3d113d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TLOR ← (( do (pure (_get_SCR_EL3_Type_TLOR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TLOR ← (( do (pure (_get_HCR_EL2_Type_TLOR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_LORC_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_LORC_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_LORC_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg LORC_EL1 (Mk_LORC_EL1_Type (← (X_read t 64))))))))
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
                      else writeReg LORC_EL1 (Mk_LORC_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg LORC_EL1 (Mk_LORC_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def LOREA_EL1_SysRegWrite_12823f1415052a0d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TLOR ← (( do (pure (_get_SCR_EL3_Type_TLOR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TLOR ← (( do (pure (_get_HCR_EL2_Type_TLOR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_LOREA_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_LOREA_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_LOREA_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg LOREA_EL1 (Mk_LOREA_EL1_Type (← (X_read t 64))))))))
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
                      else writeReg LOREA_EL1 (Mk_LOREA_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg LOREA_EL1 (Mk_LOREA_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def LORN_EL1_SysRegWrite_8a9df4ed50885fe4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TLOR ← (( do (pure (_get_SCR_EL3_Type_TLOR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TLOR ← (( do (pure (_get_HCR_EL2_Type_TLOR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_LORN_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_LORN_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_LORN_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg LORN_EL1 (Mk_LORN_EL1_Type (← (X_read t 64))))))))
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
                      else writeReg LORN_EL1 (Mk_LORN_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg LORN_EL1 (Mk_LORN_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def LORSA_EL1_SysRegWrite_8563a4250c047bc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TLOR ← (( do (pure (_get_SCR_EL3_Type_TLOR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TLOR ← (( do (pure (_get_HCR_EL2_Type_TLOR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_LORSA_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_LORSA_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_LORSA_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TLOR == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg LORSA_EL1 (Mk_LORSA_EL1_Type (← (X_read t 64))))))))
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
                      else writeReg LORSA_EL1 (Mk_LORSA_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg LORSA_EL1 (Mk_LORSA_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR2_EL1_SysRegWrite_e1a1cf3df97e5908 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x280#12) (← (X_read t 64)))
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
                      else writeReg MAIR2_EL1 (Mk_MAIR2_EL1_Type (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg MAIR2_EL1 (Mk_MAIR2_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR2_EL2_SysRegWrite_947c3848493bf9b8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AIEn ← (( do (pure (_get_SCR_EL3_Type_AIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nMAIR2_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_nMAIR2_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((← (EL2Enabled ())) && (__HCR_EL2_TVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nMAIR2_EL1 == 0#1)) : Bool)
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
                          then (NVMem_set (BitVec.toNat 0x280#12) (← (X_read t 64)))
                          else writeReg MAIR2_EL1 (Mk_MAIR2_EL1_Type (← (X_read t 64))))))))
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
                      then writeReg MAIR2_EL2 (Mk_MAIR2_EL2_Type (← (X_read t 64)))
                      else writeReg MAIR2_EL1 (Mk_MAIR2_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg MAIR2_EL1 (Mk_MAIR2_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR2_EL2_SysRegWrite_e772542d41ef21f4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg MAIR2_EL2 (Mk_MAIR2_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg MAIR2_EL2 (Mk_MAIR2_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR2_EL3_SysRegWrite_47b59b09cadb288b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg MAIR2_EL3 (Mk_MAIR2_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR_EL1_SysRegWrite_544016ebf1c83382 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_MAIR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_MAIR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TVM == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_MAIR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x140#12) (← (X_read t 64)))
                  else writeReg MAIR_EL1 (Mk_MAIR_EL1_Type (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg MAIR_EL2 (Mk_MAIR_EL2_Type (← (X_read t 64)))
              else writeReg MAIR_EL1 (Mk_MAIR_EL1_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg MAIR_EL1 (Mk_MAIR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR_EL1_SysRegWrite_853552cc3b84fd15 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x140#12) (← (X_read t 64)))
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
              then writeReg MAIR_EL1 (Mk_MAIR_EL1_Type (← (X_read t 64)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg MAIR_EL1 (Mk_MAIR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR_EL2_SysRegWrite_c3f5f844df66ccc8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg MAIR_EL2 (Mk_MAIR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg MAIR_EL2 (Mk_MAIR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MAIR_EL3_SysRegWrite_77100e09b4275a77 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg MAIR_EL3 (Mk_MAIR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MDCCINT_EL1_SysRegWrite_fbfdab04982e8c96 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
      then writeReg MDCCINT_EL1 (Mk_MDCCINT_EL1_Type (← (X_read t 64)))
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
                                  else writeReg MDCCINT_EL1 (Mk_MDCCINT_EL1_Type (← (X_read t 64)))))))))
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
                              else writeReg MDCCINT_EL1 (Mk_MDCCINT_EL1_Type (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg MDCCINT_EL1 (Mk_MDCCINT_EL1_Type (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def MDCR_EL2_SysRegWrite_b68bb751a2e2a82d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg MDCR_EL2 (Mk_MDCR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg MDCR_EL2 (Mk_MDCR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MDCR_EL3_SysRegWrite_83616ee112453f2c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg MDCR_EL3 (Mk_MDCR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MDSCR_EL1_SysRegWrite_77b35d79c41eeb78 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_MDSCR_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_MDSCR_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_MDSCR_EL1 == 1#1)) : Bool)
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
                          then (NVMem_set (BitVec.toNat 0x158#12) (← (X_read t 64)))
                          else (__set_MDSCR_EL1 (Mk_MDSCR_EL1_Type (← (X_read t 64)))))))))
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
                  else (__set_MDSCR_EL1 (Mk_MDSCR_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_MDSCR_EL1 (Mk_MDSCR_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MDSELR_EL1_SysRegWrite_96ef452973a846b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EBWE ← (( do (pure (_get_MDCR_EL3_Type_EBWE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nMDSELR_EL1 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nMDSELR_EL1 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nMDSELR_EL1 == 0#1)) : Bool)
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
                                  else (__set_MDSELR_EL1 (Mk_MDSELR_EL1_Type (← (X_read t 64)))))))))))
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
                          else (__set_MDSELR_EL1 (Mk_MDSELR_EL1_Type (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_MDSELR_EL1 (Mk_MDSELR_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECID_A0_EL2_SysRegWrite_c9ecd55f732bd0ad (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else writeReg MECID_A0_EL2 (Mk_MECID_A0_EL2_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg MECID_A0_EL2 (Mk_MECID_A0_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECID_A1_EL2_SysRegWrite_bc98456a1287bbce (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else writeReg MECID_A1_EL2 (Mk_MECID_A1_EL2_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg MECID_A1_EL2 (Mk_MECID_A1_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECID_P0_EL2_SysRegWrite_e612f6294b4993e5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else writeReg MECID_P0_EL2 (Mk_MECID_P0_EL2_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg MECID_P0_EL2 (Mk_MECID_P0_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECID_P1_EL2_SysRegWrite_3807276157365bf3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else writeReg MECID_P1_EL2 (Mk_MECID_P1_EL2_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg MECID_P1_EL2 (Mk_MECID_P1_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MECID_RL_A_EL3_SysRegWrite_be910360ddec275a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg MECID_RL_A_EL3 (Mk_MECID_RL_A_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MFAR_EL3_SysRegWrite_036c1c3c4a295873 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg MFAR_EL3 (Mk_MFAR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAM0_EL1_SysRegWrite_20837bf9c61cd88e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else writeReg MPAM0_EL1 (Mk_MPAM0_EL1_Type (← (X_read t 64)))))
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
              else writeReg MPAM0_EL1 (Mk_MPAM0_EL1_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg MPAM0_EL1 (Mk_MPAM0_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAM1_EL1_SysRegWrite_6fc49ea36a62b2f9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x900#12) (← (X_read t 64)))
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
                  else (__set_MPAM1_EL1 (Mk_MPAM1_EL1_Type (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (__set_MPAM1_EL1 (Mk_MPAM1_EL1_Type (← (X_read t 64))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def MPAM2_EL2_SysRegWrite_00c9bb10273a16c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (NVMem_set (BitVec.toNat 0x900#12) (← (X_read t 64)))
                  else (__set_MPAM1_EL1 (Mk_MPAM1_EL1_Type (← (X_read t 64)))))))
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
                  then (__set_MPAM2_EL2 (Mk_MPAM2_EL2_Type (← (X_read t 64))))
                  else (__set_MPAM1_EL1 (Mk_MPAM1_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_MPAM1_EL1 (Mk_MPAM1_EL1_Type (← (X_read t 64))))
              else (pure ()))))


