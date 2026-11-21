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
def PMSICR_EL1_SysRegRead_21061f53bd37d43f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMSICR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMSICR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPMS ← (( do (pure (_get_MDCR_EL2_Type_TPMS (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
               (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                 (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                 (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMSICR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__MDCR_EL2_TPMS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                             (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                             (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x838#12))))
                          else (X_set t 64 (__get_PMSICR_EL1 (← readReg PMSICR_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                     (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                     (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                         (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                         (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_PMSICR_EL1 (← readReg PMSICR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMSICR_EL1 (← readReg PMSICR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSIDR_EL1_SysRegRead_51ea9fe85c485c1f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMSIDR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMSIDR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPMS ← (( do (pure (_get_MDCR_EL2_Type_TPMS (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
               (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                 (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                 (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMSIDR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__MDCR_EL2_TPMS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                             (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                             (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_PMSIDR_EL1 (← readReg PMSIDR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                     (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                     (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                         (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                         (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_PMSIDR_EL1 (← readReg PMSIDR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMSIDR_EL1 (← readReg PMSIDR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSIRR_EL1_SysRegRead_fb1e9f4098f84549 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMSIRR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMSIRR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPMS ← (( do (pure (_get_MDCR_EL2_Type_TPMS (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
               (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                 (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                 (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMSIRR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__MDCR_EL2_TPMS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                             (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                             (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x840#12))))
                          else (X_set t 64 (__get_PMSIRR_EL1 (← readReg PMSIRR_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                     (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                     (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                         (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                         (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_PMSIRR_EL1 (← readReg PMSIRR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMSIRR_EL1 (← readReg PMSIRR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSLATFR_EL1_SysRegRead_84b6a2bf8c3de92b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMSLATFR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMSLATFR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPMS ← (( do (pure (_get_MDCR_EL2_Type_TPMS (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
               (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                 (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                 (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMSLATFR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__MDCR_EL2_TPMS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                             (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                             (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x848#12))))
                          else (X_set t 64 (__get_PMSLATFR_EL1 (← readReg PMSLATFR_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                     (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                     (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                         (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                         (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_PMSLATFR_EL1 (← readReg PMSLATFR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMSLATFR_EL1 (← readReg PMSLATFR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSNEVFR_EL1_SysRegRead_be9e8b2bf9a915f4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSN ← (( do (pure (_get_MDCR_EL3_Type_EnPMSN (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nPMSNEVFR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_nPMSNEVFR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPMS ← (( do (pure (_get_MDCR_EL2_Type_TPMS (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
               (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                 (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                 (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPMSN == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nPMSNEVFR_EL1 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_TPMS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                                 (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                                 (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_EnPMSN == 0#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
                                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x850#12))))
                                  else (X_set t 64 (← (__get_PMSNEVFR_EL1 (← readReg PMSNEVFR_EL1)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                     (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                     (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPMSN == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 0)]) == 0#1)) <||> (do
                             (pure ((BitVec.join1 [(BitVec.access (_get_MDCR_EL3_Type_NSPB (← readReg MDCR_EL3)) 1)]) != (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))))) <||> (do
                             (pure ((← (IsFeatureImplemented FEAT_RME)) && (__MDCR_EL3_NSPBE != __SCR_EL3_NSE))))))) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_EnPMSN == 0#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (← (__get_PMSNEVFR_EL1 (← readReg PMSNEVFR_EL1))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (__get_PMSNEVFR_EL1 (← readReg PMSNEVFR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSSCR_EL1_SysRegRead_a6c1e79f31190a60 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSCR_EL1 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSCR_EL1 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSCR_EL1 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_PMSSCR_EL1 (← readReg PMSSCR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_PMSSCR_EL1 (← readReg PMSSCR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMSSCR_EL1 (← readReg PMSSCR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMUACR_EL1_SysRegRead_ce94146f70da9e11 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMUACR_EL1 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMUACR_EL1 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMUACR_EL1 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else (X_set t 64 (__get_PMUACR_EL1 (← readReg PMUACR_EL1))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_PMUACR_EL1 (← readReg PMUACR_EL1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMUACR_EL1 (← readReg PMUACR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMUSERENR_EL0_SysRegRead_4984184853b93fa2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMUSERENR_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMUSERENR_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMUSERENR_EL0 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_PMUSERENR_EL0 (← readReg PMUSERENR_EL0)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMUSERENR_EL0 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_PMUSERENR_EL0 (← readReg PMUSERENR_EL0)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_PMUSERENR_EL0 (← readReg PMUSERENR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMUSERENR_EL0 (← readReg PMUSERENR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMXEVCNTR_EL0_SysRegRead_52bf82e65ceb6b97 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) ≥b 31) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_FGT)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((IsFeatureImplemented FEAT_PMUv3p9) <&&> (do
                   (pure (((_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0)) +++ ((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)))) == 0b000#3))) <||> (do
                   (pure (! (← (IsFeatureImplemented FEAT_PMUv3p9)))) <&&> (do
                     (pure (((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) == 0b00#2)))))) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVCNTRn_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
                          then
                            (do
                              if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                              then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                              else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVCNTRn_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
                          then
                            (do
                              if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                              then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                              else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def PMXEVTYPER_EL0_SysRegRead_822f8e38c465529c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((←((pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) != 31)) <&&> (do
       (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) ≥b 31))))) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_FGT)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((IsFeatureImplemented FEAT_PMUv3p9) <&&> (do
                   (pure (((_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) == 0b00#2))) <||> (do
                   (pure ((! (← (IsFeatureImplemented FEAT_PMUv3p9))) && (__PMUSERENR_EL0_EN == 0#1)))))) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) != 31))) <&&> (do
                               (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
                          then
                            (do
                              if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                              then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                              else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) == 31) : Bool)
                                  then (X_set t 64 (__get_PMCCFILTR_EL0 (← readReg PMCCFILTR_EL0)))
                                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) != 31))) <&&> (do
                               (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
                          then
                            (do
                              if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                              then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                              else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) == 31) : Bool)
                                  then (X_set t 64 (__get_PMCCFILTR_EL0 (← readReg PMCCFILTR_EL0)))
                                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) == 31) : Bool)
                          then (X_set t 64 (__get_PMCCFILTR_EL0 (← readReg PMCCFILTR_EL0)))
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) == 31) : Bool)
                      then (X_set t 64 (__get_PMCCFILTR_EL0 (← readReg PMCCFILTR_EL0)))
                      else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def PM_SysRegRead_801ea1615b4051f7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (((Zeros (n := 31)) +++ (← readReg PSTATE).PM) +++ (Zeros (n := 32))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (((Zeros (n := 31)) +++ (← readReg PSTATE).PM) +++ (Zeros (n := 32))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (((Zeros (n := 31)) +++ (← readReg PSTATE).PM) +++ (Zeros (n := 32))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def POR_EL0_SysRegRead_b50bc065c1491be2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_PIEn ← (( do (pure (_get_SCR_EL3_Type_PIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __CPACR_EL1_E0POE ← (( do (pure (_get_CPACR_EL1_Type_E0POE (← readReg CPACR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nPOR_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_nPOR_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_E0POE ← (( do (pure (_get_CPTR_EL2_Type_E0POE (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_PIEn == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CPACR_EL1_E0POE == 0#1)) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TRVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nPOR_EL0 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CPTR_EL2_E0POE == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (← readReg POR_EL0))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_PIEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nPOR_EL0 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg POR_EL0))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_PIEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg POR_EL0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg POR_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def POR_EL1_SysRegRead_4e2353406e7396e0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_PIEn ← (( do (pure (_get_SCR_EL3_Type_PIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x2A8#12))))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg POR_EL1))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg POR_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def POR_EL2_SysRegRead_1719ba3e87a9ae64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_PIEn ← (( do (pure (_get_SCR_EL3_Type_PIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nPOR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nPOR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_PIEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nPOR_EL1 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x2A8#12))))
                          else (X_set t 64 (← readReg POR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_PIEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (← readReg POR_EL2))
                      else (X_set t 64 (← readReg POR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg POR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def POR_EL2_SysRegRead_b9e6082fd3098e22 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_PIEn ← (( do (pure (_get_SCR_EL3_Type_PIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_PIEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg POR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg POR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def POR_EL3_SysRegRead_dd4204e711df2c15 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg POR_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def RCWMASK_EL1_SysRegRead_5e28ff06021a9b89 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_RCWMASKEn ← (( do (pure (_get_SCR_EL3_Type_RCWMASKEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nRCWMASK_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nRCWMASK_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nRCWMASK_EL1 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (Sail.BitVec.extractLsb (← readReg RCWMASK_EL1) 63 0)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (Sail.BitVec.extractLsb (← readReg RCWMASK_EL1) 63 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (Sail.BitVec.extractLsb (← readReg RCWMASK_EL1) 63 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def RCWSMASK_EL1_SysRegRead_431036cb88e83e2a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_RCWMASKEn ← (( do (pure (_get_SCR_EL3_Type_RCWMASKEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR2_EL2_nRCWSMASK_EL1 ← (( do (pure (_get_HFGRTR2_EL2_Type_nRCWSMASK_EL1 (← readReg HFGRTR2_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HFGRTR2_EL2_nRCWSMASK_EL1 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (Sail.BitVec.extractLsb (← readReg RCWSMASK_EL1) 63 0))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (Sail.BitVec.extractLsb (← readReg RCWSMASK_EL1) 63 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (Sail.BitVec.extractLsb (← readReg RCWSMASK_EL1) 63 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def REVIDR_EL1_SysRegRead_ec0a78562653e4de (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID1 ← (( do (pure (_get_HCR_EL2_Type_TID1 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_REVIDR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_REVIDR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID1 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_REVIDR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (← readReg REVIDR_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg REVIDR_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg REVIDR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def RGSR_EL1_SysRegRead_64fa1a7b4e06fd7e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else (X_set t 64 (__get_RGSR_EL1 (← readReg RGSR_EL1))))))
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
                  else (X_set t 64 (__get_RGSR_EL1 (← readReg RGSR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_RGSR_EL1 (← readReg RGSR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def RMR_EL1_SysRegRead_9adb359c4ff7cc32 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((((← readReg PSTATE).EL == EL1) && (IsHighestEL EL1)) : Bool)
  then (X_set t 64 (__get_RMR_EL1 (← readReg RMR_EL1)))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def RMR_EL2_SysRegRead_0cc9a425a7ab6f44 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
           (EL2Enabled ())))) && (IsHighestEL EL2)) && (__HCR_EL2_NV == 1#1)) : Bool)
  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
  else
    (do
      if ((((← readReg PSTATE).EL == EL2) && (IsHighestEL EL2)) : Bool)
      then (X_set t 64 (__get_RMR_EL2 (← readReg RMR_EL2)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def RMR_EL3_SysRegRead_412ca53e076c7a6e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((((← readReg PSTATE).EL == EL3) && (IsHighestEL EL3)) : Bool)
  then (X_set t 64 (__get_RMR_EL3 (← readReg RMR_EL3)))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def RNDRRS_SysRegRead_8cd65845e0b85be3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TRNDR ← (( do (pure (_get_SCR_EL3_Type_TRNDR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((← (IsFeatureImplemented FEAT_RNG_TRAP)) && (__SCR_EL3_TRNDR == 1#1)) : Bool)
      then
        (do
          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
      else
        (do
          if ((! (← (IsFeatureImplemented FEAT_RNG))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (X_set t 64 (← readReg RNDRRS))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (IsFeatureImplemented FEAT_RNG_TRAP)) && (__SCR_EL3_TRNDR == 1#1)) : Bool)
          then
            (do
              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
          else
            (do
              if ((! (← (IsFeatureImplemented FEAT_RNG))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (X_set t 64 (← readReg RNDRRS))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((← (IsFeatureImplemented FEAT_RNG_TRAP)) && (__SCR_EL3_TRNDR == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else
                (do
                  if ((! (← (IsFeatureImplemented FEAT_RNG))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (← readReg RNDRRS))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((← (IsFeatureImplemented FEAT_RNG_TRAP)) && (__SCR_EL3_TRNDR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((! (← (IsFeatureImplemented FEAT_RNG))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (X_set t 64 (← readReg RNDRRS))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def RNDR_SysRegRead_cb03dcf786233956 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TRNDR ← (( do (pure (_get_SCR_EL3_Type_TRNDR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((← (IsFeatureImplemented FEAT_RNG_TRAP)) && (__SCR_EL3_TRNDR == 1#1)) : Bool)
      then
        (do
          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
      else
        (do
          if ((! (← (IsFeatureImplemented FEAT_RNG))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (X_set t 64 (← readReg RNDR))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (IsFeatureImplemented FEAT_RNG_TRAP)) && (__SCR_EL3_TRNDR == 1#1)) : Bool)
          then
            (do
              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
          else
            (do
              if ((! (← (IsFeatureImplemented FEAT_RNG))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (X_set t 64 (← readReg RNDR))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((← (IsFeatureImplemented FEAT_RNG_TRAP)) && (__SCR_EL3_TRNDR == 1#1)) : Bool)
              then
                (do
                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
              else
                (do
                  if ((! (← (IsFeatureImplemented FEAT_RNG))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (← readReg RNDR))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((← (IsFeatureImplemented FEAT_RNG_TRAP)) && (__SCR_EL3_TRNDR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((! (← (IsFeatureImplemented FEAT_RNG))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (X_set t 64 (← readReg RNDR))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def RVBAR_EL1_SysRegRead_c839c12def98ebc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((((← readReg PSTATE).EL == EL1) && (IsHighestEL EL1)) : Bool)
  then (X_set t 64 (← readReg RVBAR_EL1))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def RVBAR_EL2_SysRegRead_4cac2371e78214e1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
           (EL2Enabled ())))) && (IsHighestEL EL2)) && (__HCR_EL2_NV == 1#1)) : Bool)
  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
  else
    (do
      if ((((← readReg PSTATE).EL == EL2) && (IsHighestEL EL2)) : Bool)
      then (X_set t 64 (← readReg RVBAR_EL2))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def RVBAR_EL3_SysRegRead_d57b9abefb0ea569 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((((← readReg PSTATE).EL == EL3) && (IsHighestEL EL3)) : Bool)
  then (X_set t 64 (← readReg RVBAR_EL3))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def S2PIR_EL2_SysRegRead_2ac98b74605e5456 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_PIEn ← (( do (pure (_get_SCR_EL3_Type_PIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x2B0#12))))
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_PIEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg S2PIR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg S2PIR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def S2POR_EL1_SysRegRead_e4b7b03dbe33ccaa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_PIEn ← (( do (pure (_get_SCR_EL3_Type_PIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nS2POR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nS2POR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_PIEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nS2POR_EL1 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x2B8#12))))
                          else (X_set t 64 (← readReg S2POR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_PIEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg S2POR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg S2POR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AArch64_ImpDefSysRegRead (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (t : Int) : SailM Unit := do
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def SCR_EL3_SysRegRead_b8dcdb7a98ef0967 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (__get_SCR_EL3 (← readReg SCR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR2_EL1_SysRegRead_90cdeb4a4ee1955f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_SCTLR2En ← (( do (pure (_get_SCR_EL3_Type_SCTLR2En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x278#12))))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_SCTLR2En == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_SCTLR2En == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_SCTLR2_EL1 (← readReg SCTLR2_EL1)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_SCTLR2_EL1 (← readReg SCTLR2_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR2_EL1_SysRegRead_e0ec1b448b49d808 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_SCTLR2En ← (( do (pure (_get_SCR_EL3_Type_SCTLR2En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_SCTLR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_SCTLR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_SCTLR2En ← (( do (pure (_get_HCRX_EL2_Type_SCTLR2En (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_SCTLR2En == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_SCTLR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_SCTLR2En == 0#1)))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_SCTLR2En == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x278#12))))
                              else (X_set t 64 (__get_SCTLR2_EL1 (← readReg SCTLR2_EL1)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_SCTLR2En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_SCTLR2En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (__get_SCTLR2_EL2 (← readReg SCTLR2_EL2)))
                      else (X_set t 64 (__get_SCTLR2_EL1 (← readReg SCTLR2_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SCTLR2_EL1 (← readReg SCTLR2_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR2_EL2_SysRegRead_4e11a5aa656bf495 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_SCTLR2En ← (( do (pure (_get_SCR_EL3_Type_SCTLR2En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_SCTLR2En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_SCTLR2En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_SCTLR2_EL2 (← readReg SCTLR2_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SCTLR2_EL2 (← readReg SCTLR2_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR2_EL3_SysRegRead_87ae87d52be38631 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (__get_SCTLR2_EL3 (← readReg SCTLR2_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR_EL1_SysRegRead_043383b392ab2b8a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x110#12))))
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
              then (X_set t 64 (← (__get_SCTLR_EL1 (← readReg SCTLR_EL1))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← (__get_SCTLR_EL1 (← readReg SCTLR_EL1))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR_EL1_SysRegRead_ce1d601189e8030e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_SCTLR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_SCTLR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_SCTLR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x110#12))))
                  else (X_set t 64 (← (__get_SCTLR_EL1 (← readReg SCTLR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (__get_SCTLR_EL2 (← readReg SCTLR_EL2)))
              else (X_set t 64 (← (__get_SCTLR_EL1 (← readReg SCTLR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (__get_SCTLR_EL1 (← readReg SCTLR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR_EL2_SysRegRead_e3c3d9b65d84cd42 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_SCTLR_EL2 (← readReg SCTLR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SCTLR_EL2 (← readReg SCTLR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR_EL3_SysRegRead_6ae2b7096922ae74 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (__get_SCTLR_EL3 (← readReg SCTLR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCXTNUM_EL0_SysRegRead_73b90ab9431e2a86 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EnSCXT ← (( do (pure (_get_SCR_EL3_Type_EnSCXT (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCTLR_EL1_TSCXT ← (( do (pure (_get_SCTLR_EL1_Type_TSCXT (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_EnSCXT ← (( do (pure (_get_HCR_EL2_Type_EnSCXT (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_SCXTNUM_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_SCXTNUM_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_TSCXT ← (( do (pure (_get_SCTLR_EL2_Type_TSCXT (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_TSCXT == 1#1)) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_EnSCXT == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_SCXTNUM_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_TSCXT == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (← readReg SCXTNUM_EL0))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_EnSCXT == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_SCXTNUM_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg SCXTNUM_EL0))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg SCXTNUM_EL0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg SCXTNUM_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCXTNUM_EL1_SysRegRead_32a07f15f90850b2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EnSCXT ← (( do (pure (_get_SCR_EL3_Type_EnSCXT (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x188#12))))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg SCXTNUM_EL1))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg SCXTNUM_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCXTNUM_EL2_SysRegRead_8bf0422effd0ab20 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EnSCXT ← (( do (pure (_get_SCR_EL3_Type_EnSCXT (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg SCXTNUM_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg SCXTNUM_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCXTNUM_EL2_SysRegRead_af67262612e5c00e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EnSCXT ← (( do (pure (_get_SCR_EL3_Type_EnSCXT (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_EnSCXT ← (( do (pure (_get_HCR_EL2_Type_EnSCXT (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_SCXTNUM_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_SCXTNUM_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b011#3))))) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_EnSCXT == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_SCXTNUM_EL1 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x188#12))))
                              else (X_set t 64 (← readReg SCXTNUM_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (← readReg SCXTNUM_EL2))
                      else (X_set t 64 (← readReg SCXTNUM_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg SCXTNUM_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCXTNUM_EL3_SysRegRead_ad99c3bb5365f4d5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg SCXTNUM_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SDER32_EL2_SysRegRead_6dbf529a9fc6ce3e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if (((←((pure (! (HaveEL EL2))) <||> (do
         (pure (! (← (IsFeatureImplemented FEAT_SEL2))))))) || (! (HaveAArch32EL EL1))) : Bool)
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
              if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
                  if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else (X_set t 64 (__get_SDER32_EL2 (← readReg SDER32_EL2)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (X_set t 64 (__get_SDER32_EL2 (← readReg SDER32_EL2))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def SDER32_EL3_SysRegRead_e8c9baf258d1c833 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if (((! (HaveEL EL3)) || (! (HaveAArch32EL EL1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
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
                  then (X_set t 64 (__get_SDER32_EL3 (← (SDER32_EL3_read ()))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def SMCR_EL1_SysRegRead_924df8670c1f630f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_ESM ← (( do (pure (_get_CPTR_EL3_Type_ESM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPACR_EL1_SMEN ← (( do (pure (_get_CPACR_EL1_Type_SMEN (← readReg CPACR_EL1))) ) : SailM (BitVec 2) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TSM ← (( do (pure (_get_CPTR_EL2_Type_TSM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_SMEN ← (( do (pure (_get_CPTR_EL2_Type_SMEN (← readReg CPTR_EL2))) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_ESM == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((let b__2 := __CPACR_EL1_SMEN
                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                 then true
                 else false : Bool) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x1D#8))
              else
                (do
                  if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 0#1)) && (__CPTR_EL2_TSM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                  else
                    (do
                      if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 1#1)) && (let b__1 := __CPTR_EL2_SMEN
                           if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8)))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1F0#12))))
                              else (X_set t 64 (__get_SMCR_EL1 (← readReg SMCR_EL1)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_ESM == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TSM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_SMEN
                           if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8)))
                          else
                            (do
                              if ((__HCR_EL2_E2H == 1#1) : Bool)
                              then (X_set t 64 (__get_SMCR_EL2 (← readReg SMCR_EL2)))
                              else (X_set t 64 (__get_SMCR_EL1 (← readReg SMCR_EL1))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))
                  else (X_set t 64 (__get_SMCR_EL1 (← readReg SMCR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMCR_EL1_SysRegRead_ea88aa9e02fbf3b4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_ESM ← (( do (pure (_get_CPTR_EL3_Type_ESM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_SMEN ← (( do (pure (_get_CPTR_EL2_Type_SMEN (← readReg CPTR_EL2))) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1F0#12))))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((let b__0 := __CPTR_EL2_SMEN
                         if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8)))
                          else (X_set t 64 (__get_SMCR_EL1 (← readReg SMCR_EL1))))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then
                    (do
                      if ((__CPTR_EL3_ESM == 0#1) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))
                      else (X_set t 64 (__get_SMCR_EL1 (← readReg SMCR_EL1))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMCR_EL2_SysRegRead_c0f6766b3afb8b13 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_ESM ← (( do (pure (_get_CPTR_EL3_Type_ESM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TSM ← (( do (pure (_get_CPTR_EL2_Type_TSM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_SMEN ← (( do (pure (_get_CPTR_EL2_Type_SMEN (← readReg CPTR_EL2))) ) : SailM (BitVec 2) )
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_ESM == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TSM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_SMEN
                           if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8)))
                          else (X_set t 64 (__get_SMCR_EL2 (← readReg SMCR_EL2)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))
                  else (X_set t 64 (__get_SMCR_EL2 (← readReg SMCR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMCR_EL3_SysRegRead_131f4d5255bb9624 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_ESM ← (( do (pure (_get_CPTR_EL3_Type_ESM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
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
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))
                  else (X_set t 64 (__get_SMCR_EL3 (← readReg SMCR_EL3))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMIDR_EL1_SysRegRead_35f7ac0cb705482a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID1 ← (( do (pure (_get_HCR_EL2_Type_TID1 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
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
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID1 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_SMIDR_EL1 (← readReg SMIDR_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_SMIDR_EL1 (← readReg SMIDR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SMIDR_EL1 (← readReg SMIDR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMPRIMAP_EL2_SysRegRead_c09b27037a76a5c0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_ESM ← (( do (pure (_get_CPTR_EL3_Type_ESM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1F8#12))))
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_ESM == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg SMPRIMAP_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (← readReg SMPRIMAP_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMPRI_EL1_SysRegRead_ce73dae3ecbf18f6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_ESM ← (( do (pure (_get_CPTR_EL3_Type_ESM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nSMPRI_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nSMPRI_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_ESM == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nSMPRI_EL1 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_SMPRI_EL1 (← readReg SMPRI_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_ESM == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_SMPRI_EL1 (← readReg SMPRI_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_SMPRI_EL1 (← readReg SMPRI_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMACCESSR_EL1_SysRegRead_26644746ac7f02e9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMACCESSR_EL1 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMACCESSR_EL1 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMACCESSR_EL1 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x8E8#12))))
                              else (X_set t 64 (← readReg SPMACCESSR_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (← readReg SPMACCESSR_EL2))
                      else (X_set t 64 (← readReg SPMACCESSR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg SPMACCESSR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMACCESSR_EL1_SysRegRead_c8d8e0186d23b218 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x8E8#12))))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg SPMACCESSR_EL1))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg SPMACCESSR_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMACCESSR_EL2_SysRegRead_aebb0159a0970aae (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg SPMACCESSR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg SPMACCESSR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMACCESSR_EL3_SysRegRead_04a853a73f22109c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg SPMACCESSR_EL3))
              else (pure ()))))

/-- Type quantifiers: s : Int -/
def SPMCFGR_EL1_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMCGCR_EL1_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMCNTENCLR_EL0_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMCNTENSET_EL0_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMCR_EL0_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMDEVAFF_EL1_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMDEVARCH_EL1_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: n : Int, s : Int -/
def SPMEVCNTR_EL0_read (s : Int) (n : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: n : Int, s : Int -/
def SPMEVFILT2R_EL0_read (s : Int) (n : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: n : Int, s : Int -/
def SPMEVFILTR_EL0_read (s : Int) (n : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: n : Int, s : Int -/
def SPMEVTYPER_EL0_read (s : Int) (n : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMIIDR_EL1_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMINTENCLR_EL1_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMINTENSET_EL1_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMOVSCLR_EL0_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMOVSSET_EL0_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMROOTCR_EL3_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: s : Int -/
def SPMSCR_EL1_read (s : Int) : (BitVec 64) :=
  (Zeros (n := 64))

/-- Type quantifiers: t : Int -/
def SPMSELR_EL0_SysRegRead_423f70f41ec02ca1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMSELR_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMSELR_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__MDSCR_EL1_EnSPM == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMSELR_EL0 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_SPMSELR_EL0 (← readReg SPMSELR_EL0)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMSELR_EL0 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_SPMSELR_EL0 (← readReg SPMSELR_EL0))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_SPMSELR_EL0 (← readReg SPMSELR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SPMSELR_EL0 (← readReg SPMSELR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_EL1_SysRegRead_563abdf3a232cd99 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x160#12))))
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
              then (X_set t 64 (__get_SPSR_EL1 (← readReg SPSR_EL1)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_SPSR_EL1 (← readReg SPSR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_EL2_SysRegRead_c62428913c72a08e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x160#12))))
              else (X_set t 64 (__get_SPSR_EL1 (← readReg SPSR_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (__get_SPSR_EL2 (← readReg SPSR_EL2)))
              else (X_set t 64 (__get_SPSR_EL1 (← readReg SPSR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SPSR_EL1 (← readReg SPSR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_EL2_SysRegRead_f8dd5a5a3ce06a92 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_SPSR_EL1 (← readReg SPSR_EL1)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_SPSR_EL2 (← readReg SPSR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SPSR_EL2 (← readReg SPSR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_EL3_SysRegRead_df09fc431da6e372 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (__get_SPSR_EL3 (← readReg SPSR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_abt_SysRegRead_ced162955bfdf7d0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_SPSR_abt (← readReg SPSR_abt)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SPSR_abt (← readReg SPSR_abt)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_fiq_SysRegRead_efae9f97878743e3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_SPSR_fiq (← readReg SPSR_fiq)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SPSR_fiq (← readReg SPSR_fiq)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_irq_SysRegRead_3f8614ad01700094 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_SPSR_irq (← readReg SPSR_irq)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SPSR_irq (← readReg SPSR_irq)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_und_SysRegRead_ffbc14073ddb1072 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_SPSR_und (← readReg SPSR_und)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_SPSR_und (← readReg SPSR_und)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSel_SysRegRead_40cc9773567bb9cf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_SP ← (( do (pure (← readReg PSTATE).SP) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 ((Zeros (n := 63)) +++ __PSTATE_SP))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 ((Zeros (n := 63)) +++ __PSTATE_SP))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 ((Zeros (n := 63)) +++ __PSTATE_SP))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SP_EL0_SysRegRead_83d763503fa7e549 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_SP ← (( do (pure (← readReg PSTATE).SP) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((__PSTATE_SP == 0#1) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (X_set t 64 (← readReg SP_EL0)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__PSTATE_SP == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (X_set t 64 (← readReg SP_EL0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__PSTATE_SP == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (← readReg SP_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SP_EL1_SysRegRead_424b458c54382730 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x240#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg SP_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg SP_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SP_EL2_SysRegRead_d604bd0fb0757c08 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg SP_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SSBS_SysRegRead_2e7b32f98c2852d5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (X_set t 64 (((Zeros (n := 51)) +++ (← readReg PSTATE).SSBS) +++ (Zeros (n := 12))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (((Zeros (n := 51)) +++ (← readReg PSTATE).SSBS) +++ (Zeros (n := 12))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (((Zeros (n := 51)) +++ (← readReg PSTATE).SSBS) +++ (Zeros (n := 12))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (((Zeros (n := 51)) +++ (← readReg PSTATE).SSBS) +++ (Zeros (n := 12))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SVCR_SysRegRead_bfac8039b65bb2b5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_ESM ← (( do (pure (_get_CPTR_EL3_Type_ESM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPACR_EL1_SMEN ← (( do (pure (_get_CPACR_EL1_Type_SMEN (← readReg CPACR_EL1))) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_SMEN ← (( do (pure (_get_CPTR_EL2_Type_SMEN (← readReg CPTR_EL2))) ) : SailM (BitVec 2) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TSM ← (( do (pure (_get_CPTR_EL2_Type_TSM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_ESM == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CPACR_EL1_SMEN != 0b11#2)) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x1D#8)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CPTR_EL2_SMEN != 0b11#2)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
              else
                (do
                  if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 1#1)) && (let b__3 := __CPTR_EL2_SMEN
                       if (((Sail.BitVec.extractLsb b__3 0 0) == (0#1 : (BitVec 1))) : Bool)
                       then true
                       else false : Bool)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                  else
                    (do
                      if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 0#1)) && (__CPTR_EL2_TSM == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8)))
                          else (X_set t 64 ((Zeros (n := 62)) +++ ((← readReg PSTATE).ZA +++ (← readReg PSTATE).SM)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_ESM == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((let b__2 := __CPACR_EL1_SMEN
                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                 then true
                 else false : Bool) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x1D#8))
              else
                (do
                  if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 0#1)) && (__CPTR_EL2_TSM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                  else
                    (do
                      if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 1#1)) && (let b__1 := __CPTR_EL2_SMEN
                           if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8)))
                          else (X_set t 64 ((Zeros (n := 62)) +++ ((← readReg PSTATE).ZA +++ (← readReg PSTATE).SM))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_ESM == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TSM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_SMEN
                           if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8)))
                          else (X_set t 64 ((Zeros (n := 62)) +++ ((← readReg PSTATE).ZA +++ (← readReg PSTATE).SM)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))
                  else (X_set t 64 ((Zeros (n := 62)) +++ ((← readReg PSTATE).ZA +++ (← readReg PSTATE).SM))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCO_SysRegRead_fec6636824256193 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (X_set t 64 (((Zeros (n := 38)) +++ (← readReg PSTATE).TCO) +++ (Zeros (n := 25))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (((Zeros (n := 38)) +++ (← readReg PSTATE).TCO) +++ (Zeros (n := 25))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (((Zeros (n := 38)) +++ (← readReg PSTATE).TCO) +++ (Zeros (n := 25))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (((Zeros (n := 38)) +++ (← readReg PSTATE).TCO) +++ (Zeros (n := 25))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR2_EL1_SysRegRead_c832348f3796463e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TCR2En ← (( do (pure (_get_SCR_EL3_Type_TCR2En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x270#12))))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_TCR2_EL1 (← readReg TCR2_EL1)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_TCR2_EL1 (← readReg TCR2_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR2_EL2_SysRegRead_5dd157d2d7e53a90 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TCR2En ← (( do (pure (_get_SCR_EL3_Type_TCR2En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_TCR2_EL2 (← readReg TCR2_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_TCR2_EL2 (← readReg TCR2_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR2_EL2_SysRegRead_d12dd160e7a3b2d0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TCR2En ← (( do (pure (_get_SCR_EL3_Type_TCR2En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_TCR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_TCR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_TCR2En ← (( do (pure (_get_HCRX_EL2_Type_TCR2En (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TCR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_TCR2En == 0#1)))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x270#12))))
                              else (X_set t 64 (__get_TCR2_EL1 (← readReg TCR2_EL1)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (__get_TCR2_EL2 (← readReg TCR2_EL2)))
                      else (X_set t 64 (__get_TCR2_EL1 (← readReg TCR2_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_TCR2_EL1 (← readReg TCR2_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR_EL1_SysRegRead_3c972cf7b788a8a1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x120#12))))
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
              then (X_set t 64 (__get_TCR_EL1 (← readReg TCR_EL1)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_TCR_EL1 (← readReg TCR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR_EL1_SysRegRead_906af64cf526e3f6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_TCR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_TCR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TCR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x120#12))))
                  else (X_set t 64 (__get_TCR_EL1 (← readReg TCR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (__get_TCR_EL2 (← readReg TCR_EL2)))
              else (X_set t 64 (__get_TCR_EL1 (← readReg TCR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_TCR_EL1 (← readReg TCR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR_EL2_SysRegRead_424c76a4449d67b2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_TCR_EL2 (← readReg TCR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_TCR_EL2 (← readReg TCR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR_EL3_SysRegRead_0d04522059172f43 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (__get_TCR_EL3 (← readReg TCR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TFSRE0_EL1_SysRegRead_e7166fad237839bf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else (X_set t 64 (__get_TFSRE0_EL1 (← readReg TFSRE0_EL1))))))
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
                  else (X_set t 64 (__get_TFSRE0_EL1 (← readReg TFSRE0_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_TFSRE0_EL1 (← readReg TFSRE0_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TFSR_EL1_SysRegRead_629d1d7950939eef (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ATA ← (( do (pure (_get_SCR_EL3_Type_ATA (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x190#12))))
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
                      else (X_set t 64 (__get_TFSR_EL1 (← readReg TFSR_EL1)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_TFSR_EL1 (← readReg TFSR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TFSR_EL2_SysRegRead_5ac7c240abc0c535 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ATA ← (( do (pure (_get_SCR_EL3_Type_ATA (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_ATA ← (( do (pure (_get_HCR_EL2_Type_ATA (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b011#3))))) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
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
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x190#12))))
                          else (X_set t 64 (__get_TFSR_EL1 (← readReg TFSR_EL1))))))))
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
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (__get_TFSR_EL2 (← readReg TFSR_EL2)))
                      else (X_set t 64 (__get_TFSR_EL1 (← readReg TFSR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_TFSR_EL1 (← readReg TFSR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TFSR_EL2_SysRegRead_c301d170f18e0e34 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ATA ← (( do (pure (_get_SCR_EL3_Type_ATA (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_ATA ← (( do (pure (_get_HCR_EL2_Type_ATA (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
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
                      else (X_set t 64 (__get_TFSR_EL1 (← readReg TFSR_EL1))))))
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
                  else (X_set t 64 (__get_TFSR_EL2 (← readReg TFSR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_TFSR_EL2 (← readReg TFSR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TFSR_EL3_SysRegRead_8cd0ca2e5d9daf2c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (__get_TFSR_EL3 (← readReg TFSR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDR2_EL0_SysRegRead_71cf61d7c1b2b93d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EnTP2 ← (( do (pure (_get_SCR_EL3_Type_EnTP2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCTLR_EL1_EnTP2 ← (( do (pure (_get_SCTLR_EL1_Type_EnTP2 (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_EnTP2 ← (( do (pure (_get_SCTLR_EL2_Type_EnTP2 (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nTPIDR2_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_nTPIDR2_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnTP2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_EnTP2 == 0#1)) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_EnTP2 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nTPIDR2_EL0 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_EnTP2 == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg TPIDR2_EL0)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnTP2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nTPIDR2_EL0 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_EnTP2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg TPIDR2_EL0)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnTP2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_EnTP2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg TPIDR2_EL0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg TPIDR2_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDRRO_EL0_SysRegRead_914a0b925fac624e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_TPIDRRO_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_TPIDRRO_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TPIDRRO_EL0 == 1#1)) : Bool)
      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
      else (X_set t 64 (← readReg TPIDRRO_EL0)))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TPIDRRO_EL0 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg TPIDRRO_EL0)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg TPIDRRO_EL0))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg TPIDRRO_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDR_EL0_SysRegRead_512297cd575d98fa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_TPIDR_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_TPIDR_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TPIDR_EL0 == 1#1)) : Bool)
      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
      else (X_set t 64 (← readReg TPIDR_EL0)))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TPIDR_EL0 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg TPIDR_EL0)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg TPIDR_EL0))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg TPIDR_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDR_EL1_SysRegRead_cb207f415778832f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_TPIDR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_TPIDR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TPIDR_EL1 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (← readReg TPIDR_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg TPIDR_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg TPIDR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDR_EL2_SysRegRead_840081a307f6cade (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x090#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg TPIDR_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg TPIDR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDR_EL3_SysRegRead_165fa3219105298e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg TPIDR_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TRFCR_EL1_SysRegRead_346a67ae7b13428d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TTRF ← (( do (pure (_get_MDCR_EL3_Type_TTRF (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x880#12))))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_TRFCR_EL1 (← readReg TRFCR_EL1)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_TRFCR_EL1 (← readReg TRFCR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TRFCR_EL2_SysRegRead_3507a58ffe771821 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TTRF ← (( do (pure (_get_MDCR_EL3_Type_TTRF (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TTRF ← (( do (pure (_get_MDCR_EL2_Type_TTRF (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__MDCR_EL2_TTRF == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                      then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x880#12))))
                      else (X_set t 64 (__get_TRFCR_EL1 (← readReg TRFCR_EL1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (__get_TRFCR_EL2 (← readReg TRFCR_EL2)))
                      else (X_set t 64 (__get_TRFCR_EL1 (← readReg TRFCR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_TRFCR_EL1 (← readReg TRFCR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TRFCR_EL2_SysRegRead_adc3a07d7fc07643 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TTRF ← (( do (pure (_get_MDCR_EL3_Type_TTRF (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_TRFCR_EL2 (← readReg TRFCR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_TRFCR_EL2 (← readReg TRFCR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR0_EL1_SysRegRead_ea81bf619338bdf3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x200#12))))
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
              then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR0_EL1 (← (TTBR0_EL1_read ()))) 63 0))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR0_EL1 (← (TTBR0_EL1_read ()))) 63 0))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR0_EL2_SysRegRead_213283d6df4659a2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_TTBR0_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_TTBR0_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TTBR0_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x200#12))))
                  else (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR0_EL1 (← (TTBR0_EL1_read ()))) 63 0)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR0_EL2 (← (TTBR0_EL2_read ()))) 63 0))
              else (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR0_EL1 (← (TTBR0_EL1_read ()))) 63 0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR0_EL1 (← (TTBR0_EL1_read ()))) 63 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR0_EL2_SysRegRead_46a02b83889584ea (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR0_EL2 (← (TTBR0_EL2_read ()))) 63 0))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR0_EL2 (← (TTBR0_EL2_read ()))) 63 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR0_EL3_SysRegRead_b3013f97ed37beea (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (__get_TTBR0_EL3 (← readReg TTBR0_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR1_EL1_SysRegRead_004ea76932891707 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_TTBR1_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_TTBR1_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TTBR1_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x210#12))))
                  else (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR1_EL1 (← (TTBR1_EL1_read ()))) 63 0)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR1_EL2 (← readReg TTBR1_EL2)) 63 0))
              else (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR1_EL1 (← (TTBR1_EL1_read ()))) 63 0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR1_EL1 (← (TTBR1_EL1_read ()))) 63 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR1_EL1_SysRegRead_b7baefd515331ebe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x210#12))))
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
              then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR1_EL1 (← (TTBR1_EL1_read ()))) 63 0))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR1_EL1 (← (TTBR1_EL1_read ()))) 63 0))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR1_EL2_SysRegRead_0c064c5f1843df74 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR1_EL2 (← readReg TTBR1_EL2)) 63 0))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (Sail.BitVec.extractLsb (__get_TTBR1_EL2 (← readReg TTBR1_EL2)) 63 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def UAO_SysRegRead_4c61cdd9d285c8cc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (((Zeros (n := 40)) +++ (← readReg PSTATE).UAO) +++ (Zeros (n := 23))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (((Zeros (n := 40)) +++ (← readReg PSTATE).UAO) +++ (Zeros (n := 23))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (((Zeros (n := 40)) +++ (← readReg PSTATE).UAO) +++ (Zeros (n := 23))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VBAR_EL1_SysRegRead_f248fbb25db37a7b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x250#12))))
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
              then (X_set t 64 (__get_VBAR_EL1 (← readReg VBAR_EL1)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_VBAR_EL1 (← readReg VBAR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VBAR_EL2_SysRegRead_025a01f041322eae (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_VBAR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_VBAR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_VBAR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x250#12))))
                  else (X_set t 64 (__get_VBAR_EL1 (← readReg VBAR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (__get_VBAR_EL2 (← readReg VBAR_EL2)))
              else (X_set t 64 (__get_VBAR_EL1 (← readReg VBAR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_VBAR_EL1 (← readReg VBAR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VBAR_EL2_SysRegRead_369573c45c9746cf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_VBAR_EL2 (← readReg VBAR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_VBAR_EL2 (← readReg VBAR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VBAR_EL3_SysRegRead_1921cc85b07f3896 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (__get_VBAR_EL3 (← readReg VBAR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VDISR_EL2_SysRegRead_07ff39acd959bbaf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_AMO ← (( do (pure (_get_HCR_EL2_Type_AMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EA ← (( do (pure (_get_SCR_EL3_Type_EA (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_AMO == 1#1)) : Bool)
          then (X_set t 64 (__get_VDISR_EL2 (← readReg VDISR_EL2)))
          else
            (do
              if (((←((pure (HaveEL EL3)) <&&> (do
                     (pure (! (← (Halted ()))))))) && (__SCR_EL3_EA == 1#1)) : Bool)
              then (X_set t 64 (Zeros (n := 64)))
              else (X_set t 64 (__get_DISR_EL1 (← readReg DISR_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (HaveEL EL3)) <&&> (do
                     (pure (! (← (Halted ()))))))) && (__SCR_EL3_EA == 1#1)) : Bool)
              then (X_set t 64 (Zeros (n := 64)))
              else (X_set t 64 (__get_DISR_EL1 (← readReg DISR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_DISR_EL1 (← readReg DISR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VDISR_EL2_SysRegRead_354cfd34639eb7c6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x500#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_VDISR_EL2 (← readReg VDISR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_VDISR_EL2 (← readReg VDISR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VMECID_A_EL2_SysRegRead_aa29d8316696b535 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (X_set t 64 (__get_VMECID_A_EL2 (← readReg VMECID_A_EL2))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_VMECID_A_EL2 (← readReg VMECID_A_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VMECID_P_EL2_SysRegRead_85067caadb2f69e9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (X_set t 64 (__get_VMECID_P_EL2 (← readReg VMECID_P_EL2))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_VMECID_P_EL2 (← readReg VMECID_P_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VMPIDR_EL2_SysRegRead_4d4e4e0bcb925136 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x050#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_VMPIDR_EL2 (← readReg VMPIDR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (X_set t 64 (__get_MPIDR_EL1 (← readReg MPIDR_EL1)))
                  else (X_set t 64 (__get_VMPIDR_EL2 (← readReg VMPIDR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VMPIDR_EL2_SysRegRead_6d0c680fdfd4837e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_MPIDR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_MPIDR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_MPIDR_EL1 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((← (EL2Enabled ())) : Bool)
              then (X_set t 64 (__get_VMPIDR_EL2 (← readReg VMPIDR_EL2)))
              else (X_set t 64 (__get_MPIDR_EL1 (← readReg MPIDR_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_MPIDR_EL1 (← readReg MPIDR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_MPIDR_EL1 (← readReg MPIDR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VNCR_EL2_SysRegRead_fd49e25478d53eb1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x0B0#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_VNCR_EL2 (← readReg VNCR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_VNCR_EL2 (← readReg VNCR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VPIDR_EL2_SysRegRead_c419b4414b36ba2e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x088#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_VPIDR_EL2 (← readReg VPIDR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (X_set t 64 (__get_MIDR_EL1 (← readReg MIDR_EL1)))
                  else (X_set t 64 (__get_VPIDR_EL2 (← readReg VPIDR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VSESR_EL2_SysRegRead_dcbab774e333f499 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x508#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_VSESR_EL2 (← readReg VSESR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_VSESR_EL2 (← readReg VSESR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VSTCR_EL2_SysRegRead_15cf4d2aac84d328 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x048#12))))
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
              if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (X_set t 64 (__get_VSTCR_EL2 (← readReg VSTCR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (__get_VSTCR_EL2 (← readReg VSTCR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VSTTBR_EL2_SysRegRead_5dcb8c3ead41869d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x030#12))))
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
              if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (X_set t 64 (__get_VSTTBR_EL2 (← readReg VSTTBR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (__get_VSTTBR_EL2 (← readReg VSTTBR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VTCR_EL2_SysRegRead_f801b4fb3334c4c3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x040#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_VTCR_EL2 (← readReg VTCR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_VTCR_EL2 (← readReg VTCR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VTTBR_EL2_SysRegRead_1816600c5e2db377 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x020#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (Sail.BitVec.extractLsb (__get_VTTBR_EL2 (← (VTTBR_EL2_read ()))) 63 0))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (Sail.BitVec.extractLsb (__get_VTTBR_EL2 (← (VTTBR_EL2_read ()))) 63 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ZCR_EL1_SysRegRead_ae33ffd6ee977eba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_EZ ← (( do (pure (_get_CPTR_EL3_Type_EZ (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_ZEN ← (( do (pure (_get_CPTR_EL2_Type_ZEN (← readReg CPTR_EL2))) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1E0#12))))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_EZ == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((let b__0 := __CPTR_EL2_ZEN
                         if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_EZ == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8)))
                          else (X_set t 64 (__get_ZCR_EL1 (← readReg ZCR_EL1))))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then
                    (do
                      if ((__CPTR_EL3_EZ == 0#1) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8))
                      else (X_set t 64 (__get_ZCR_EL1 (← readReg ZCR_EL1))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ZCR_EL1_SysRegRead_f79acfc1d948e192 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_EZ ← (( do (pure (_get_CPTR_EL3_Type_EZ (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPACR_EL1_ZEN ← (( do (pure (_get_CPACR_EL1_Type_ZEN (← readReg CPACR_EL1))) ) : SailM (BitVec 2) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TZ ← (( do (pure (_get_CPTR_EL2_Type_TZ (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_ZEN ← (( do (pure (_get_CPTR_EL2_Type_ZEN (← readReg CPTR_EL2))) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_EZ == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((let b__2 := __CPACR_EL1_ZEN
                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                 then true
                 else false : Bool) : Bool)
              then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x19#8))
              else
                (do
                  if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 0#1)) && (__CPTR_EL2_TZ == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8))
                  else
                    (do
                      if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 1#1)) && (let b__1 := __CPTR_EL2_ZEN
                           if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_EZ == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8)))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1E0#12))))
                              else (X_set t 64 (__get_ZCR_EL1 (← readReg ZCR_EL1)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_EZ == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TZ == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_ZEN
                           if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_EZ == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8)))
                          else
                            (do
                              if ((__HCR_EL2_E2H == 1#1) : Bool)
                              then (X_set t 64 (__get_ZCR_EL2 (← readReg ZCR_EL2)))
                              else (X_set t 64 (__get_ZCR_EL1 (← readReg ZCR_EL1))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_EZ == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8))
                  else (X_set t 64 (__get_ZCR_EL1 (← readReg ZCR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ZCR_EL2_SysRegRead_e12f14b3f5451ee5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_EZ ← (( do (pure (_get_CPTR_EL3_Type_EZ (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TZ ← (( do (pure (_get_CPTR_EL2_Type_TZ (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_ZEN ← (( do (pure (_get_CPTR_EL2_Type_ZEN (← readReg CPTR_EL2))) ) : SailM (BitVec 2) )
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_EZ == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TZ == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_ZEN
                           if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_EZ == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8)))
                          else (X_set t 64 (__get_ZCR_EL2 (← readReg ZCR_EL2)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_EZ == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8))
                  else (X_set t 64 (__get_ZCR_EL2 (← readReg ZCR_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ZCR_EL3_SysRegRead_db53f2dcbaed5b3a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_EZ ← (( do (pure (_get_CPTR_EL3_Type_EZ (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
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
                  if ((__CPTR_EL3_EZ == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8))
                  else (X_set t 64 (__get_ZCR_EL3 (← readReg ZCR_EL3))))
              else (pure ()))))

/-- Type quantifiers: k_read : Bool, t : Int -/
def AArch64_UnallocatedSysRegAccess (op0 : (BitVec 2)) (op1 : (BitVec 3)) (crn : (BitVec 4)) (op2 : (BitVec 3)) (crm : (BitVec 4)) (read : Bool) (t : Int) : SailM Unit := SailME.run do
  let rcs_el0_trap ← (( do (undefined_bool ()) ) : SailME Unit Bool )
  let tid3_trap : Bool := false
  let tid3_trap ← (( do
    if ((←((pure (((← readReg PSTATE).EL == EL1) && read)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure ((_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2)) == 1#1))))) : Bool)
    then
      (do
        if ((← (HaveFGTExt ())) : Bool)
        then (pure true)
        else (__IMPDEF_boolean "Unallocated encodings trapped by HCR_EL2.TID3"))
    else (pure tid3_trap) ) : SailME Unit Bool )
  if (((←((pure ((← readReg PSTATE).EL == EL1)) <||> (do
         (pure ((← readReg PSTATE).EL == EL2)) <||> (do
           (pure ((← readReg PSTATE).EL == EL3)))))) && read) : Bool)
  then
    (do
      if ((((op0 == 0b11#2) && (op1 == 0b000#3)) && (crn == 0b0000#4)) : Bool)
      then
        (do
          if (((crm == 0b0010#4) && (op2 == 0b111#3)) : Bool)
          then
            (do
              if (tid3_trap : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else SailME.throw (← (do (X_set t 64 (Zeros (n := 64))))))
          else
            (do
              if (((crm == 0b0011#4) && ((op2 == 0b011#3) || ((op2 == 0b101#3) || ((op2 == 0b110#3) || (op2 == 0b111#3))))) : Bool)
              then
                (do
                  if (tid3_trap : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else SailME.throw (← (do (X_set t 64 (Zeros (n := 64))))))
              else
                (do
                  if (((crm == 0b0100#4) && ((op2 == 0b010#3) || ((op2 == 0b011#3) || ((op2 == 0b101#3) || ((op2 == 0b110#3) || (op2 == 0b111#3)))))) : Bool)
                  then
                    (do
                      if (tid3_trap : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else SailME.throw (← (do (X_set t 64 (Zeros (n := 64))))))
                  else
                    (do
                      if (((crm == 0b0101#4) && ((op2 == 0b010#3) || ((op2 == 0b011#3) || ((op2 == 0b110#3) || (op2 == 0b111#3))))) : Bool)
                      then
                        (do
                          if (tid3_trap : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else SailME.throw (← (do (X_set t 64 (Zeros (n := 64))))))
                      else
                        (do
                          if (((crm == 0b0110#4) && ((op2 == 0b010#3) || ((op2 == 0b011#3) || ((op2 == 0b100#3) || ((op2 == 0b101#3) || ((op2 == 0b110#3) || (op2 == 0b111#3))))))) : Bool)
                          then
                            (do
                              if (tid3_trap : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else SailME.throw (← (do (X_set t 64 (Zeros (n := 64))))))
                          else
                            (do
                              if (((crm == 0b0111#4) && ((op2 == 0b011#3) || ((op2 == 0b100#3) || ((op2 == 0b101#3) || ((op2 == 0b110#3) || (op2 == 0b111#3)))))) : Bool)
                              then
                                (do
                                  if (tid3_trap : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else SailME.throw (← (do (X_set t 64 (Zeros (n := 64))))))
                              else (pure ())))))))
      else (pure ()))
  else (pure ())
  let in_feature_space : Bool :=
    ((((op0 == 0b11#2) && (let b__1 := op1
          if (((Sail.BitVec.extractLsb b__1 2 1) == (0b00#2 : (BitVec 2))) : Bool)
          then true
          else
            (if ((b__1 == (0b011#3 : (BitVec 3))) : Bool)
            then true
            else false) : Bool)) && (crn == 0b0000#4)) && (let b__3 := crm
      if (((Sail.BitVec.extractLsb b__3 3 3) == (0#1 : (BitVec 1))) : Bool)
      then true
      else false : Bool))
  let ec_val : Int := (BitVec.toNat 0x0#4)
  let ec_val ← (( do
    if ((← (HaveIDSExt ())) : Bool)
    then (pure (BitVec.toNat 0x18#8))
    else (pure ec_val) ) : SailME Unit Int )
  let ec_val := ec_val
  if ((in_feature_space && read) : Bool)
  then
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
               (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
          then (AArch64_SystemAccessTrap EL2 ec_val)
          else (AArch64_SystemAccessTrap EL1 ec_val))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
          then
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                   (pure ((_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2)) == 1#1))))) : Bool)
              then (AArch64_SystemAccessTrap EL2 ec_val)
              else (AArch64_SystemAccessTrap EL1 ec_val))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
              then (AArch64_SystemAccessTrap EL2 ec_val)
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (AArch64_SystemAccessTrap EL3 ec_val)
                  else (pure ())))))
  else (pure ())
  if (((←((HaveFeatTIDCP1 ()) <&&> (do
         (pure ((← readReg PSTATE).EL == EL0))))) && (let b__0 := crn
       if ((((Sail.BitVec.extractLsb b__0 3 3) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
       then true
       else false : Bool)) : Bool)
  then
    (do
      if ((←((pure (! (← (IsInHost ())))) <&&> (do
           (pure ((_get_SCTLR_EL1_Type_TIDCP (← readReg SCTLR_EL1)) == 1#1))))) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (pure ())
      if ((←((IsInHost ()) <&&> (do
           (pure ((_get_SCTLR_EL2_Type_TIDCP (← readReg SCTLR_EL2)) == 1#1))))) : Bool)
      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
      else (pure ()))
  else (pure ())
  if ((((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
           (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
           (EL2Enabled ())) <&&> (do
           (pure ((_get_HCR_EL2_Type_TIDCP (← readReg HCR_EL2)) == 1#1))))) && ((op0 == 0b01#2) || (op0 == 0b11#2))) && ((crn == 0b1011#4) || (crn == 0b1111#4))) : Bool)
  then
    (do
      let rcs_el0_trap ← (( do (__IMPDEF_boolean "Reserved Control Space EL0 Trapped") ) : SailME Unit Bool )
      if ((((← readReg PSTATE).EL == EL1) || rcs_el0_trap) : Bool)
      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
      else (pure ()))
  else (pure ())
  if (((((BitVec.slice op0 0 2) == 0b01#2) || ((BitVec.slice op0 0 2) == 0b11#2)) && (((BitVec.slice crn 0 4) == 0b1011#4) || ((BitVec.slice crn 0 4) == 0b1111#4))) : Bool)
  then (sailThrow ((Error_ImplementationDefined "")) : SailM Unit)
  else (pure ())
  let rcs_el0_trap := rcs_el0_trap
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ACCDATA_EL1_SysRegWrite_8e0ffec0877851f7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ADEn ← (( do (pure (_get_SCR_EL3_Type_ADEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nACCDATA_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_nACCDATA_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_ADEn == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nACCDATA_EL1 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_ADEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg ACCDATA_EL1 (Mk_ACCDATA_EL1_Type (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_ADEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_ADEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg ACCDATA_EL1 (Mk_ACCDATA_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ACCDATA_EL1 (Mk_ACCDATA_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ACTLR_EL1_SysRegWrite_7b28af04d67b98b9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TACR ← (( do (pure (_get_HCR_EL2_Type_TACR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TACR == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set (BitVec.toNat 0x118#12) (← (X_read t 64)))
              else writeReg ACTLR_EL1 (← (X_read t 64))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg ACTLR_EL1 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ACTLR_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ACTLR_EL2_SysRegWrite_55fae67ae0a6faf2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg ACTLR_EL2 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg ACTLR_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ACTLR_EL3_SysRegWrite_32865ae0e6068940 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg ACTLR_EL3 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR0_EL1_SysRegWrite_be844a45265221f7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x128#12) (← (X_read t 64)))
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
              then writeReg AFSR0_EL1 (← (X_read t 64))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg AFSR0_EL1 (← (X_read t 64))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR0_EL1_SysRegWrite_bfb8a5c21b8a15cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_AFSR0_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_AFSR0_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_AFSR0_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x128#12) (← (X_read t 64)))
                  else writeReg AFSR0_EL1 (← (X_read t 64)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg AFSR0_EL2 (← (X_read t 64))
              else writeReg AFSR0_EL1 (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AFSR0_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR0_EL2_SysRegWrite_1b5a40d7cb8265ce (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg AFSR0_EL2 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AFSR0_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR0_EL3_SysRegWrite_1c6f9ccfd5716ce3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg AFSR0_EL3 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR1_EL1_SysRegWrite_358d58edce00a180 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x130#12) (← (X_read t 64)))
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
              then writeReg AFSR1_EL1 (← (X_read t 64))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg AFSR1_EL1 (← (X_read t 64))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR1_EL1_SysRegWrite_57c6bddf9a2482df (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_AFSR1_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_AFSR1_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_AFSR1_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x130#12) (← (X_read t 64)))
                  else writeReg AFSR1_EL1 (← (X_read t 64)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg AFSR1_EL2 (← (X_read t 64))
              else writeReg AFSR1_EL1 (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AFSR1_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR1_EL2_SysRegWrite_a63eac436b30cded (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg AFSR1_EL2 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AFSR1_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR1_EL3_SysRegWrite_9124b1facd539906 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg AFSR1_EL3 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ALLINT_SysRegWrite_28e93c037c43b390 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCRX_EL2_TALLINT ← (( do (pure (_get_HCRX_EL2_Type_TALLINT (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_TALLINT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else writeReg PSTATE { (← readReg PSTATE) with ALLINT := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 13)]))) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with ALLINT := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 13)]))) }
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg PSTATE { (← readReg PSTATE) with ALLINT := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 13)]))) }
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR2_EL1_SysRegWrite_15a11ef20a82181c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x288#12) (← (X_read t 64)))
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
                      else writeReg AMAIR2_EL1 (← (X_read t 64))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg AMAIR2_EL1 (← (X_read t 64))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR2_EL2_SysRegWrite_1e7d4e25c1dcc572 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg AMAIR2_EL2 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AMAIR2_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR2_EL2_SysRegWrite_d6e02923e8c9c534 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AIEn ← (( do (pure (_get_SCR_EL3_Type_AIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nAMAIR2_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_nAMAIR2_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nAMAIR2_EL1 == 0#1)) : Bool)
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
                          then (NVMem_set (BitVec.toNat 0x288#12) (← (X_read t 64)))
                          else writeReg AMAIR2_EL1 (← (X_read t 64)))))))
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
                      then writeReg AMAIR2_EL2 (← (X_read t 64))
                      else writeReg AMAIR2_EL1 (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AMAIR2_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR2_EL3_SysRegWrite_2519753087e4450a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg AMAIR2_EL3 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR_EL1_SysRegWrite_88ac7594e16a57fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x148#12) (← (X_read t 64)))
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
              then writeReg AMAIR_EL1 (← (X_read t 64))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg AMAIR_EL1 (← (X_read t 64))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR_EL2_SysRegWrite_3448b91e0a445f88 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_AMAIR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_AMAIR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_AMAIR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x148#12) (← (X_read t 64)))
                  else writeReg AMAIR_EL1 (← (X_read t 64)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg AMAIR_EL2 (← (X_read t 64))
              else writeReg AMAIR_EL1 (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AMAIR_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR_EL2_SysRegWrite_4119e8051bae499e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg AMAIR_EL2 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AMAIR_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR_EL3_SysRegWrite_31ae559cd6a97a1f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg AMAIR_EL3 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCNTENCLR0_EL0_SysRegWrite_87e21241643a862e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then writeReg AMCNTENCLR0_EL0 (Mk_AMCNTENCLR0_EL0_Type (← (X_read t 64)))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMCNTENCLR1_EL0_SysRegWrite_c63fb61a666d3a21 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then writeReg AMCNTENCLR1_EL0 (Mk_AMCNTENCLR1_EL0_Type (← (X_read t 64)))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMCNTENSET0_EL0_SysRegWrite_b4e12b5dd3b0738a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then writeReg AMCNTENSET0_EL0 (Mk_AMCNTENSET0_EL0_Type (← (X_read t 64)))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMCNTENSET1_EL0_SysRegWrite_a3bee0219e2d4b9e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then writeReg AMCNTENSET1_EL0 (Mk_AMCNTENSET1_EL0_Type (← (X_read t 64)))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMCR_EL0_SysRegWrite_6a9019dd97aa8af1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then writeReg AMCR_EL0 (Mk_AMCR_EL0_Type (← (X_read t 64)))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_57776cdcd88bec7e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then (AMEVCNTR0_EL0_set 2 (Mk_AMEVCNTR0_EL0_Type (← (X_read t 64))))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_a28bd21dde7b55b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then (AMEVCNTR0_EL0_set 1 (Mk_AMEVCNTR0_EL0_Type (← (X_read t 64))))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_ca5a4224a458ea03 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then (AMEVCNTR0_EL0_set 0 (Mk_AMEVCNTR0_EL0_Type (← (X_read t 64))))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_df6bb2663cab03ed (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then (AMEVCNTR0_EL0_set 3 (Mk_AMEVCNTR0_EL0_Type (← (X_read t 64))))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_2bb86c4004ef9258 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 0))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 0 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_2cb2cddc132a8d44 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 6))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 6 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_3743486d55da4508 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 1 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_44cf3260f4372341 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 5))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 5 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_4a152435dd65137a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 10))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 10 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_5139d9a03c76c81b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 3))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 3 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_59bacd045e260141 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 4))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 4 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_6bd5d306c662d714 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 2 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_887d0ce81624d210 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 15))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 15 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_909b4a89534d73e1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 9))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 9 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_9193b8497c20a5ba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 14))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 14 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_cef156af264e97db (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 11))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 11 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_d8f3e0edb71c094d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 8))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 8 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_e45e9615b0ec1e8a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 12))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 12 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_f1dd22a5ecbcbc6b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 13))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 13 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_fe71412c61f10c5a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 7))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) 7 (Mk_AMEVCNTR1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_0923dbc89132e313 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (NVMem_set ((BitVec.toNat 0xA00#12) +i (8 *i 3)) (← (X_read t 64)))
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg AMEVCNTVOFF0_EL2 (vectorUpdate (← readReg AMEVCNTVOFF0_EL2) 3 (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AMEVCNTVOFF0_EL2 (vectorUpdate (← readReg AMEVCNTVOFF0_EL2) 3 (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_16f386a96bc6f4d5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_1aa3b39d45f679b5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_31c0cdbd9c1a5aa3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_4c087411a832c41e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_7037d0a12cbf01ad (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_74ccc6eecceec9f9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_972cb3f0c159a0b7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_9d4925d599bf21f3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_9dd8ffd73516d6df (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_a45d1ca97a349f4b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_ad5b87d3125380af (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_bbcf6bc1df66bebc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_c10f27e36cfd4438 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (NVMem_set ((BitVec.toNat 0xA00#12) +i (8 *i 2)) (← (X_read t 64)))
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg AMEVCNTVOFF0_EL2 (vectorUpdate (← readReg AMEVCNTVOFF0_EL2) 2 (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AMEVCNTVOFF0_EL2 (vectorUpdate (← readReg AMEVCNTVOFF0_EL2) 2 (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_c76c398d7598cd2b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegWrite_f6918a05ffc46bd6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (NVMem_set ((BitVec.toNat 0xA00#12) +i (8 *i 0)) (← (X_read t 64)))
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg AMEVCNTVOFF0_EL2 (vectorUpdate (← readReg AMEVCNTVOFF0_EL2) 0 (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AMEVCNTVOFF0_EL2 (vectorUpdate (← readReg AMEVCNTVOFF0_EL2) 0 (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_028cfcaff48c5d3b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 9))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 9)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 9 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 9 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_18b1c0f6609cfc70 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 8))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 8)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 8 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 8 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_1a046ba7336f9e16 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 12))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 12)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 12 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 12 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_21fc3e4e66b7bf2e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 4))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 4)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 4 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 4 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_2ba85b85b5072821 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 10))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 10)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 10 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 10 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_386268cd3029fb99 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 11))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 11)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 11 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 11 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_55f6fd2dd91b0e50 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 6))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 6)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 6 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 6 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_715140b6e1ae357e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 14))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 14)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 14 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 14 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_894c1ceeabf341e5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 13))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 13)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 13 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 13 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_a4b7dbcc8064b06d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 3))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 3)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 3 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 3 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_bcd39cd29daf1662 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 1))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 1)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 1 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 1 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_c6e6c9e8e68d2fab (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 0))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 0)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 0 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 0 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_e78a33d39c6749cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 5))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 5)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 5 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 5 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_e7b42f6640c3913b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 2))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 2)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 2 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 2 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_f1ccc2e130743f64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 15))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 15)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 15 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 15 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_fe51081bae489e73 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorOffsetImplemented 7))) : Bool)
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
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
              then (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 7)) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_AMVOFFEN == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 7 (← (X_read t 64)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg AMEVCNTVOFF1_EL2 (vectorUpdate (← readReg AMEVCNTVOFF1_EL2) 7 (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_017c244c296ed80f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 5))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 5 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_15f530ac1097257c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 13))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 13 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_3a4a4f972b395f75 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 12))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 12 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_622d8153064a03a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 2 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_6269036dfbd59a24 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 9))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 9 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_7e132038a6af9b7c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 8))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 8 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_85fbd4e6563d2700 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 15))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 15 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_8b9bd86620491fc7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 11))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 11 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_a9e61442f4e1c8cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 6))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 6 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_bc02f6fe6d8b784f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 7))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 7 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_be5c5b889ae5d0cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 1 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_c43b886db277fa04 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 0))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 0 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_e549f9ca48c70852 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 14))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 14 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_ed2615d4120abbd7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 3))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 3 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_f55a7574a9b217fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 4))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 4 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_f744e58350c3c492 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (IsG1ActivityMonitorImplemented 10))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
           (pure (! (← (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed"))))))) : Bool)
      then writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) 10 (Mk_AMEVTYPER1_EL0_Type (← (X_read t 64))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def AMUSERENR_EL0_SysRegWrite_048ed8e6dc551988 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg AMUSERENR_EL0 (Mk_AMUSERENR_EL0_Type (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg AMUSERENR_EL0 (Mk_AMUSERENR_EL0_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg AMUSERENR_EL0 (Mk_AMUSERENR_EL0_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APDAKeyHi_EL1_SysRegWrite_9127291587c7ea6e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_APDAKey ← (( do (pure (_get_HFGWTR_EL2_Type_APDAKey (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_APK == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_APDAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg APDAKeyHi_EL1 (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg APDAKeyHi_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg APDAKeyHi_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APDAKeyLo_EL1_SysRegWrite_0e1165080dd4ea81 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_APDAKey ← (( do (pure (_get_HFGWTR_EL2_Type_APDAKey (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_APK == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_APDAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg APDAKeyLo_EL1 (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg APDAKeyLo_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg APDAKeyLo_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APDBKeyHi_EL1_SysRegWrite_dcaaae97706e7922 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_APDBKey ← (( do (pure (_get_HFGWTR_EL2_Type_APDBKey (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_APK == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_APDBKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg APDBKeyHi_EL1 (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg APDBKeyHi_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg APDBKeyHi_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APDBKeyLo_EL1_SysRegWrite_e5f3a17864e0bd24 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_APDBKey ← (( do (pure (_get_HFGWTR_EL2_Type_APDBKey (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_APK == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_APDBKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg APDBKeyLo_EL1 (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg APDBKeyLo_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg APDBKeyLo_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APGAKeyHi_EL1_SysRegWrite_5d36b28ead1bb298 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_APGAKey ← (( do (pure (_get_HFGWTR_EL2_Type_APGAKey (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_APK == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_APGAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg APGAKeyHi_EL1 (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg APGAKeyHi_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg APGAKeyHi_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APGAKeyLo_EL1_SysRegWrite_8f5946d931efbfec (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_APGAKey ← (( do (pure (_get_HFGWTR_EL2_Type_APGAKey (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_APK == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_APGAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg APGAKeyLo_EL1 (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg APGAKeyLo_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg APGAKeyLo_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APIAKeyHi_EL1_SysRegWrite_dd50986e83c65aba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_APIAKey ← (( do (pure (_get_HFGWTR_EL2_Type_APIAKey (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_APK == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_APIAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg APIAKeyHi_EL1 (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg APIAKeyHi_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg APIAKeyHi_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APIAKeyLo_EL1_SysRegWrite_19be32b7aee48c9e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_APIAKey ← (( do (pure (_get_HFGWTR_EL2_Type_APIAKey (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_APK == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_APIAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg APIAKeyLo_EL1 (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg APIAKeyLo_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg APIAKeyLo_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APIBKeyHi_EL1_SysRegWrite_0d10c61af3148541 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_APIBKey ← (( do (pure (_get_HFGWTR_EL2_Type_APIBKey (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_APK == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_APIBKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg APIBKeyHi_EL1 (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg APIBKeyHi_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg APIBKeyHi_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APIBKeyLo_EL1_SysRegWrite_7cc3f2a575353b80 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_APIBKey ← (( do (pure (_get_HFGWTR_EL2_Type_APIBKey (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_APK == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_APIBKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg APIBKeyLo_EL1 (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_APK == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg APIBKeyLo_EL1 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg APIBKeyLo_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBCR_EL1_SysRegWrite_bacf32e45cccac33 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (NVMem_set (BitVec.toNat 0x8E0#12) (← (X_read t 64)))
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
                  if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__1 := __MDCR_EL3_SBRBE
                             if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                             then true
                             else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                     if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                                     then true
                                     else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else writeReg BRBCR_EL1 (Mk_BRBCR_EL1_Type (← (X_read t 64)))))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg BRBCR_EL1 (Mk_BRBCR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBCR_EL2_SysRegWrite_0f11184bdbd7fffd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_nBRBCTL ← (( do (pure (_get_HDFGWTR_EL2_Type_nBRBCTL (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__3 := __MDCR_EL3_SBRBE
                     if (((Sail.BitVec.extractLsb b__3 0 0) == (0#1 : (BitVec 1))) : Bool)
                     then true
                     else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_nBRBCTL == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__2 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                              then (NVMem_set (BitVec.toNat 0x8E0#12) (← (X_read t 64)))
                              else writeReg BRBCR_EL1 (Mk_BRBCR_EL1_Type (← (X_read t 64)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__1 := __MDCR_EL3_SBRBE
                         if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__HCR_EL2_E2H == 1#1) : Bool)
                              then writeReg BRBCR_EL2 (Mk_BRBCR_EL2_Type (← (X_read t 64)))
                              else writeReg BRBCR_EL1 (Mk_BRBCR_EL1_Type (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg BRBCR_EL1 (Mk_BRBCR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBCR_EL2_SysRegWrite_df7df73141024675 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__1 := __MDCR_EL3_SBRBE
                         if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg BRBCR_EL2 (Mk_BRBCR_EL2_Type (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg BRBCR_EL2 (Mk_BRBCR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBFCR_EL1_SysRegWrite_feda6cd6c387772e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_nBRBCTL ← (( do (pure (_get_HDFGWTR_EL2_Type_nBRBCTL (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__3 := __MDCR_EL3_SBRBE
                     if (((Sail.BitVec.extractLsb b__3 0 0) == (0#1 : (BitVec 1))) : Bool)
                     then true
                     else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_nBRBCTL == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__2 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg BRBFCR_EL1 (Mk_BRBFCR_EL1_Type (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__1 := __MDCR_EL3_SBRBE
                         if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg BRBFCR_EL1 (Mk_BRBFCR_EL1_Type (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg BRBFCR_EL1 (Mk_BRBFCR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINFINJ_EL1_SysRegWrite_9211713f1bfc2916 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGWTR_EL2_Type_nBRBDATA (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__3 := __MDCR_EL3_SBRBE
                     if (((Sail.BitVec.extractLsb b__3 0 0) == (0#1 : (BitVec 1))) : Bool)
                     then true
                     else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_nBRBDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__2 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (__set_BRBINFINJ_EL1 (Mk_BRBINFINJ_EL1_Type (← (X_read t 64)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__1 := __MDCR_EL3_SBRBE
                         if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (__set_BRBINFINJ_EL1 (Mk_BRBINFINJ_EL1_Type (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_BRBINFINJ_EL1 (Mk_BRBINFINJ_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRCINJ_EL1_SysRegWrite_68622081934254f0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGWTR_EL2_Type_nBRBDATA (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__3 := __MDCR_EL3_SBRBE
                     if (((Sail.BitVec.extractLsb b__3 0 0) == (0#1 : (BitVec 1))) : Bool)
                     then true
                     else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_nBRBDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__2 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (__set_BRBSRCINJ_EL1 (Mk_BRBSRCINJ_EL1_Type (← (X_read t 64)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__1 := __MDCR_EL3_SBRBE
                         if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (__set_BRBSRCINJ_EL1 (Mk_BRBSRCINJ_EL1_Type (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_BRBSRCINJ_EL1 (Mk_BRBSRCINJ_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGTINJ_EL1_SysRegWrite_3fc8f3855af3c754 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGWTR_EL2_Type_nBRBDATA (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__3 := __MDCR_EL3_SBRBE
                     if (((Sail.BitVec.extractLsb b__3 0 0) == (0#1 : (BitVec 1))) : Bool)
                     then true
                     else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_nBRBDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__2 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (__set_BRBTGTINJ_EL1 (Mk_BRBTGTINJ_EL1_Type (← (X_read t 64)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__1 := __MDCR_EL3_SBRBE
                         if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (__set_BRBTGTINJ_EL1 (Mk_BRBTGTINJ_EL1_Type (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_BRBTGTINJ_EL1 (Mk_BRBTGTINJ_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTS_EL1_SysRegWrite_377bbfb5528b4be3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGWTR_EL2_Type_nBRBDATA (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__3 := __MDCR_EL3_SBRBE
                     if (((Sail.BitVec.extractLsb b__3 0 0) == (0#1 : (BitVec 1))) : Bool)
                     then true
                     else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_nBRBDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__2 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg BRBTS_EL1 (Mk_BRBTS_EL1_Type (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (let b__1 := __MDCR_EL3_SBRBE
                         if (((Sail.BitVec.extractLsb b__1 0 0) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool)) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else writeReg BRBTS_EL1 (Mk_BRBTS_EL1_Type (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg BRBTS_EL1 (Mk_BRBTS_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTFRQ_EL0_SysRegWrite_f59bce36e5e3ca32 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then writeReg CNTFRQ_EL0 (← (X_read t 64))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def CNTHCTL_EL2_SysRegWrite_c57f8627acf05dc2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type (← (X_read t 64)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg CNTHCTL_EL2 (Mk_CNTHCTL_EL2_Type (← (X_read t 64)))
              else writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHCTL_EL2_SysRegWrite_ee82b0f294f84a10 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg CNTHCTL_EL2 (Mk_CNTHCTL_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTHCTL_EL2 (Mk_CNTHCTL_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHPS_CTL_EL2_SysRegWrite_409af44f6007e1b5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PCEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0PTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PTEN == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                           (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                      then (__set_CNTHPS_CTL_EL2 (Mk_CNTHPS_CTL_EL2_Type (← (X_read t 64))))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then (__set_CNTHP_CTL_EL2 (Mk_CNTHP_CTL_EL2_Type (← (X_read t 64))))
                          else (__set_CNTP_CTL_EL0 (Mk_CNTP_CTL_EL0_Type (← (X_read t 64))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x180#12) (← (X_read t 64)))
                  else (__set_CNTP_CTL_EL0 (Mk_CNTP_CTL_EL0_Type (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then (__set_CNTHPS_CTL_EL2 (Mk_CNTHPS_CTL_EL2_Type (← (X_read t 64))))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then (__set_CNTHP_CTL_EL2 (Mk_CNTHP_CTL_EL2_Type (← (X_read t 64))))
                  else (__set_CNTP_CTL_EL0 (Mk_CNTP_CTL_EL0_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_CNTP_CTL_EL0 (Mk_CNTP_CTL_EL0_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHPS_CTL_EL2_SysRegWrite_c59654dd3579a2a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
              if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (__set_CNTHPS_CTL_EL2 (Mk_CNTHPS_CTL_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (__set_CNTHPS_CTL_EL2 (Mk_CNTHPS_CTL_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHPS_CVAL_EL2_SysRegWrite_b8b5a6dbe1e48dd1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
              if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHPS_TVAL_EL2_SysRegWrite_f57d636a80644cd9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
              if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_CTL_EL2_SysRegWrite_52dddcddc87d9536 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (__set_CNTHP_CTL_EL2 (Mk_CNTHP_CTL_EL2_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_CNTHP_CTL_EL2 (Mk_CNTHP_CTL_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_CVAL_EL2_SysRegWrite_52ce6fca4007d2da (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_CVAL_EL2_SysRegWrite_ead9355a45d8e73b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PCEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0PTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PTEN == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                           (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                      then writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type (← (X_read t 64)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type (← (X_read t 64)))
                          else writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type (← (X_read t 64)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x178#12) (← (X_read t 64)))
                  else writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type (← (X_read t 64)))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type (← (X_read t 64)))
                  else writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_EL2_SysRegWrite_7488d8357bdbd8b8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHVS_CTL_EL2_SysRegWrite_9787f6cf7c77decc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
              if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (__set_CNTHVS_CTL_EL2 (Mk_CNTHVS_CTL_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (__set_CNTHVS_CTL_EL2 (Mk_CNTHVS_CTL_EL2_Type (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHVS_CTL_EL2_SysRegWrite_e967874807c6082c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0VTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VTEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                       (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                  then (__set_CNTHVS_CTL_EL2 (Mk_CNTHVS_CTL_EL2_Type (← (X_read t 64))))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                      then (__set_CNTHV_CTL_EL2 (Mk_CNTHV_CTL_EL2_Type (← (X_read t 64))))
                      else (__set_CNTV_CTL_EL0 (Mk_CNTV_CTL_EL0_Type (← (X_read t 64)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
              then (NVMem_set (BitVec.toNat 0x170#12) (← (X_read t 64)))
              else (__set_CNTV_CTL_EL0 (Mk_CNTV_CTL_EL0_Type (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then (__set_CNTHVS_CTL_EL2 (Mk_CNTHVS_CTL_EL2_Type (← (X_read t 64))))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then (__set_CNTHV_CTL_EL2 (Mk_CNTHV_CTL_EL2_Type (← (X_read t 64))))
                  else (__set_CNTV_CTL_EL0 (Mk_CNTV_CTL_EL0_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_CNTV_CTL_EL0 (Mk_CNTV_CTL_EL0_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHVS_CVAL_EL2_SysRegWrite_5acd4d20ee782a13 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
              if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHVS_TVAL_EL2_SysRegWrite_e71ca762af073cad (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
              if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHV_CTL_EL2_SysRegWrite_33f75e4b41646088 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (__set_CNTHV_CTL_EL2 (Mk_CNTHV_CTL_EL2_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_CNTHV_CTL_EL2 (Mk_CNTHV_CTL_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHV_CVAL_EL2_SysRegWrite_16bd78456d53d9ab (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0VTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VTEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                       (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                  then writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type (← (X_read t 64)))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                      then writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type (← (X_read t 64)))
                      else writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (← (X_read t 64))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
              then (NVMem_set (BitVec.toNat 0x168#12) (← (X_read t 64)))
              else writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (← (X_read t 64)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type (← (X_read t 64)))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type (← (X_read t 64)))
                  else writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHV_CVAL_EL2_SysRegWrite_a0eabf75b26da37c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHV_TVAL_EL2_SysRegWrite_6e74ff633c511335 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHV_TVAL_EL2_SysRegWrite_b6bfac5d17f766fc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0VTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VTEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                       (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                  then writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                      then writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
                      else
                        (do
                          if ((←((pure (HaveEL EL2)) <&&> (do
                               (pure (! (← (EL2Enabled ())))) <||> (do
                                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2)))))) : Bool)
                          then writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTVOFF_EL2)))
                          else writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((HaveEL EL2) : Bool)
              then writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTVOFF_EL2)))
              else writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
                  else
                    (do
                      if (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1) : Bool)
                      then writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTVOFF_EL2)))
                      else writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((←((pure (HaveEL EL2)) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
                  then writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTVOFF_EL2)))
                  else
                    (do
                      if ((←((pure (HaveEL EL2)) <&&> (do
                           (ELUsingAArch32 EL2)))) : Bool)
                      then writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))) - (← (CNTVOFF_read ()))))
                      else writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTKCTL_EL1_SysRegWrite_b6b89671d5078ba5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type (← (X_read t 64)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTPOFF_EL2_SysRegWrite_daa2a43614202ee5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ECVEn ← (( do (pure (_get_SCR_EL3_Type_ECVEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (NVMem_set (BitVec.toNat 0x1A8#12) (← (X_read t 64)))
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_ECVEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_ECVEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg CNTPOFF_EL2 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTPOFF_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTPS_CTL_EL1_SysRegWrite_22bfd6d865a619e7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ST ← (( do (pure (_get_SCR_EL3_Type_ST (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__SCR_EL3_NS == 0#1)) : Bool)
          then
            (do
              if ((__SCR_EL3_EEL2 == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__SCR_EL3_ST == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (__set_CNTPS_CTL_EL1 (Mk_CNTPS_CTL_EL1_Type (← (X_read t 64))))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_CNTPS_CTL_EL1 (Mk_CNTPS_CTL_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTPS_CVAL_EL1_SysRegWrite_0efe14958ca47dee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ST ← (( do (pure (_get_SCR_EL3_Type_ST (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__SCR_EL3_NS == 0#1)) : Bool)
          then
            (do
              if ((__SCR_EL3_EEL2 == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__SCR_EL3_ST == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg CNTPS_CVAL_EL1 (Mk_CNTPS_CVAL_EL1_Type (← (X_read t 64)))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTPS_CVAL_EL1 (Mk_CNTPS_CVAL_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTPS_TVAL_EL1_SysRegWrite_fed363b581c49e0d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ST ← (( do (pure (_get_SCR_EL3_Type_ST (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ECVEn ← (( do (pure (_get_SCR_EL3_Type_ECVEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_ECV ← (( do (pure (_get_CNTHCTL_EL2_Type_ECV (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__SCR_EL3_NS == 0#1)) : Bool)
          then
            (do
              if ((__SCR_EL3_EEL2 == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__SCR_EL3_ST == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((IsFeatureImplemented FEAT_ECV) <&&> (do
                               (EL2Enabled ())))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1)) : Bool)
                      then writeReg CNTPS_CVAL_EL1 (Mk_CNTPS_CVAL_EL1_Type (((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTPOFF_EL2)))
                      else writeReg CNTPS_CVAL_EL1 (Mk_CNTPS_CVAL_EL1_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ())))))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTPS_CVAL_EL1 (Mk_CNTPS_CVAL_EL1_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTP_CTL_EL0_SysRegWrite_6000d5c756b25763 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTHCTL_EL2_EL1NVPCT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1NVPCT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
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
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1NVPCT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (NVMem_set (BitVec.toNat 0x180#12) (← (X_read t 64))))
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
              then (__set_CNTP_CTL_EL0 (Mk_CNTP_CTL_EL0_Type (← (X_read t 64))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (__set_CNTP_CTL_EL0 (Mk_CNTP_CTL_EL0_Type (← (X_read t 64))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTP_CVAL_EL0_SysRegWrite_226b60eb1c89b722 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTHCTL_EL2_EL1NVPCT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1NVPCT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
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
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1NVPCT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (NVMem_set (BitVec.toNat 0x178#12) (← (X_read t 64))))
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
              then writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type (← (X_read t 64)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTP_TVAL_EL0_SysRegWrite_4aac8466b90febf7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTP_TVAL_EL0_SysRegWrite_eccdee10d8c7f39e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PCEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ECVEn ← (( do (pure (_get_SCR_EL3_Type_ECVEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_ECV ← (( do (pure (_get_CNTHCTL_EL2_Type_ECV (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0PTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PTEN == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                           (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                      then writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
                          else
                            (do
                              if ((←((pure (((←((IsFeatureImplemented FEAT_ECV) <&&> (do (EL2Enabled ())))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) : Bool)
                              then writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type (((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTPOFF_EL2)))
                              else writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ())))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((IsFeatureImplemented FEAT_ECV) <&&> (do
                           (EL2Enabled ())))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1)) : Bool)
                  then writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type (((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTPOFF_EL2)))
                  else writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ())))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
                  else writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type ((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTVOFF_EL2_SysRegWrite_926108484bd738bb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x060#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg CNTVOFF_EL2 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CNTVOFF_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTV_CTL_EL0_SysRegWrite_18ae5268f90eea09 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTHCTL_EL2_EL1NVVCT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1NVVCT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
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
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1NVVCT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (NVMem_set (BitVec.toNat 0x170#12) (← (X_read t 64))))
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
              then (__set_CNTV_CTL_EL0 (Mk_CNTV_CTL_EL0_Type (← (X_read t 64))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (__set_CNTV_CTL_EL0 (Mk_CNTV_CTL_EL0_Type (← (X_read t 64))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTV_CVAL_EL0_SysRegWrite_ad2fa653919bf7cc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTHCTL_EL2_EL1NVVCT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1NVVCT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
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
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1NVVCT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (NVMem_set (BitVec.toNat 0x168#12) (← (X_read t 64))))
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
              then writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (← (X_read t 64)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTV_TVAL_EL0_SysRegWrite_1d3b2670e7bc3a02 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTVOFF_EL2)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type (((sign_extend (Sail.BitVec.extractLsb (← (X_read t 64)) 31 0) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTVOFF_EL2)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CONTEXTIDR_EL1_SysRegWrite_dd8dc6c6937913e2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x108#12) (← (X_read t 64)))
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
              then writeReg CONTEXTIDR_EL1 (Mk_CONTEXTIDR_EL1_Type (← (X_read t 64)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg CONTEXTIDR_EL1 (Mk_CONTEXTIDR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CONTEXTIDR_EL2_SysRegWrite_8c6e5eeae39e62ee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg CONTEXTIDR_EL2 (Mk_CONTEXTIDR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CONTEXTIDR_EL2 (Mk_CONTEXTIDR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CONTEXTIDR_EL2_SysRegWrite_ba4861401c41da1a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_CONTEXTIDR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_CONTEXTIDR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_CONTEXTIDR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x108#12) (← (X_read t 64)))
                  else writeReg CONTEXTIDR_EL1 (Mk_CONTEXTIDR_EL1_Type (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg CONTEXTIDR_EL2 (Mk_CONTEXTIDR_EL2_Type (← (X_read t 64)))
              else writeReg CONTEXTIDR_EL1 (Mk_CONTEXTIDR_EL1_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CONTEXTIDR_EL1 (Mk_CONTEXTIDR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPACR_EL1_SysRegWrite_8a190aadf7d2b08b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TCPAC ← (( do (pure (_get_CPTR_EL3_Type_TCPAC (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (NVMem_set (BitVec.toNat 0x100#12) (← (X_read t 64)))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg CPACR_EL1 (Mk_CPACR_EL1_Type (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg CPACR_EL1 (Mk_CPACR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPACR_EL1_SysRegWrite_c63495641b6492df (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TCPAC ← (( do (pure (_get_CPTR_EL3_Type_TCPAC (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TCPAC ← (( do (pure (_get_CPTR_EL2_Type_TCPAC (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_CPACR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_CPACR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TCPAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_CPACR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                          then (NVMem_set (BitVec.toNat 0x100#12) (← (X_read t 64)))
                          else writeReg CPACR_EL1 (Mk_CPACR_EL1_Type (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then writeReg CPTR_EL2 (Mk_CPTR_EL2_Type (← (X_read t 64)))
                      else writeReg CPACR_EL1 (Mk_CPACR_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CPACR_EL1 (Mk_CPACR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPTR_EL2_SysRegWrite_26c85eb30bcb8d19 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TCPAC ← (( do (pure (_get_CPTR_EL3_Type_TCPAC (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg CPTR_EL2 (Mk_CPTR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CPTR_EL2 (Mk_CPTR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPTR_EL3_SysRegWrite_3835d83d048c2034 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg CPTR_EL3 (Mk_CPTR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CSSELR_EL1_SysRegWrite_cd9c3d82f382498a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID4 ← (( do (pure (_get_HCR_EL2_Type_TID4 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_CSSELR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_CSSELR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID2 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TID4 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_CSSELR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else writeReg CSSELR_EL1 (Mk_CSSELR_EL1_Type (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg CSSELR_EL1 (Mk_CSSELR_EL1_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg CSSELR_EL1 (Mk_CSSELR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DACR32_EL2_SysRegWrite_94b89018206732e0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg DACR32_EL2 (Mk_DACR32_EL2_Type (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then writeReg DACR32_EL2 (Mk_DACR32_EL2_Type (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DAIF_SysRegWrite_523f21b562245414 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UMA ← (( do (pure (_get_SCTLR_EL1_Type_UMA (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((EL2Enabled ()) <&&> (do
             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) || (__SCTLR_EL1_UMA == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          let split_vec ← do (pure (Sail.BitVec.extractLsb (← (X_read t 64)) 9 6))
          writeReg PSTATE { (← readReg PSTATE) with D := (Sail.BitVec.extractLsb split_vec 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with A := (Sail.BitVec.extractLsb split_vec 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb split_vec 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb split_vec 0 0) }))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let split_vec ← do (pure (Sail.BitVec.extractLsb (← (X_read t 64)) 9 6))
          writeReg PSTATE { (← readReg PSTATE) with D := (Sail.BitVec.extractLsb split_vec 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with A := (Sail.BitVec.extractLsb split_vec 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb split_vec 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb split_vec 0 0) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let split_vec ← do (pure (Sail.BitVec.extractLsb (← (X_read t 64)) 9 6))
              writeReg PSTATE { (← readReg PSTATE) with D := (Sail.BitVec.extractLsb split_vec 3 3) }
              writeReg PSTATE { (← readReg PSTATE) with A := (Sail.BitVec.extractLsb split_vec 2 2) }
              writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb split_vec 1 1) }
              writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb split_vec 0 0) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let split_vec ← do (pure (Sail.BitVec.extractLsb (← (X_read t 64)) 9 6))
                  writeReg PSTATE { (← readReg PSTATE) with D := (Sail.BitVec.extractLsb split_vec 3 3) }
                  writeReg PSTATE { (← readReg PSTATE) with A := (Sail.BitVec.extractLsb split_vec 2 2) }
                  writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb split_vec 1 1) }
                  writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb split_vec 0 0) })
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_02aee1e0e30b8f1d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 6 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 6 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 6 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_061098b9cf5c8fa1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 5 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 5 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 5 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_1e501456d6155d4d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 1 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 1 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 1 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_2d22fdf5e1f2ca10 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 15 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 15 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 15 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_35bdee83adebd0e9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 10 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 10 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 10 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_5aacf61e65fbc833 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 13 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 13 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 13 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_5dfc64a898404c6e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                                  else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 8 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))))
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
                              then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                              else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 8 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))))
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
                          then writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) (Mk_DBGBCR_EL1_Type (← (X_read t 64))))
                          else writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) 8 (Mk_DBGBCR_EL1_Type (← (X_read t 64))))))
                  else (pure ())))))


