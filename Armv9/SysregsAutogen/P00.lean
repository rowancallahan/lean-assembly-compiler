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
def ACCDATA_EL1_SysRegRead_6deec7bc548bcc31 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ADEn ← (( do (pure (_get_SCR_EL3_Type_ADEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nACCDATA_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nACCDATA_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nACCDATA_EL1 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_ADEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_ACCDATA_EL1 (← readReg ACCDATA_EL1))))))
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
                  else (X_set t 64 (__get_ACCDATA_EL1 (← readReg ACCDATA_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_ACCDATA_EL1 (← readReg ACCDATA_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ACTLR_EL1_SysRegRead_cc5a0755f0205a72 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x118#12))))
              else (X_set t 64 (← readReg ACTLR_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg ACTLR_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ACTLR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ACTLR_EL2_SysRegRead_949275ba7f389456 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← readReg ACTLR_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg ACTLR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ACTLR_EL3_SysRegRead_c20b5bca7bc57751 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg ACTLR_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR0_EL1_SysRegRead_58d465b1f7d8b040 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x128#12))))
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
              then (X_set t 64 (← readReg AFSR0_EL1))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg AFSR0_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR0_EL1_SysRegRead_859cbb0383226d9f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_AFSR0_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_AFSR0_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_AFSR0_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x128#12))))
                  else (X_set t 64 (← readReg AFSR0_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (← readReg AFSR0_EL2))
              else (X_set t 64 (← readReg AFSR0_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg AFSR0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR0_EL2_SysRegRead_acffc015481d1ac8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← readReg AFSR0_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg AFSR0_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR0_EL3_SysRegRead_2d1994fbdbde12d8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg AFSR0_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR1_EL1_SysRegRead_00f51d0e1b73738c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x130#12))))
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
              then (X_set t 64 (← readReg AFSR1_EL1))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg AFSR1_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR1_EL1_SysRegRead_3cf8f86fbb276328 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_AFSR1_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_AFSR1_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_AFSR1_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x130#12))))
                  else (X_set t 64 (← readReg AFSR1_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (← readReg AFSR1_EL2))
              else (X_set t 64 (← readReg AFSR1_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg AFSR1_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR1_EL2_SysRegRead_a12c342eb9f7885a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← readReg AFSR1_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg AFSR1_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AFSR1_EL3_SysRegRead_bbfc01f9fd46f6c4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg AFSR1_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AIDR_EL1_SysRegRead_3367279f59657745 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID1 ← (( do (pure (_get_HCR_EL2_Type_TID1 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_AIDR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_AIDR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_AIDR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (← readReg AIDR_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg AIDR_EL1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg AIDR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ALLINT_SysRegRead_ee53c92ec04c7280 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (((Zeros (n := 50)) +++ (← readReg PSTATE).ALLINT) +++ (Zeros (n := 13))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (((Zeros (n := 50)) +++ (← readReg PSTATE).ALLINT) +++ (Zeros (n := 13))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (((Zeros (n := 50)) +++ (← readReg PSTATE).ALLINT) +++ (Zeros (n := 13))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR2_EL1_SysRegRead_961066b22ab5b10e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x288#12))))
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
                      else (X_set t 64 (← readReg AMAIR2_EL1))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg AMAIR2_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR2_EL2_SysRegRead_0f9ce6311b1205f6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AIEn ← (( do (pure (_get_SCR_EL3_Type_AIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nAMAIR2_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nAMAIR2_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nAMAIR2_EL1 == 0#1)) : Bool)
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
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x288#12))))
                          else (X_set t 64 (← readReg AMAIR2_EL1)))))))
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
                      then (X_set t 64 (← readReg AMAIR2_EL2))
                      else (X_set t 64 (← readReg AMAIR2_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg AMAIR2_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR2_EL2_SysRegRead_c6e17744cc03d54f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else (X_set t 64 (← readReg AMAIR2_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg AMAIR2_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR2_EL3_SysRegRead_3e5d4dd4506a8fae (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg AMAIR2_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR_EL1_SysRegRead_9571f6fe9c5fe082 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x148#12))))
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
              then (X_set t 64 (← readReg AMAIR_EL1))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg AMAIR_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR_EL2_SysRegRead_8a38edf51a31f5e0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← readReg AMAIR_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg AMAIR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR_EL2_SysRegRead_e7d62050e609b077 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_AMAIR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_AMAIR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_AMAIR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x148#12))))
                  else (X_set t 64 (← readReg AMAIR_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (← readReg AMAIR_EL2))
              else (X_set t 64 (← readReg AMAIR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg AMAIR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR_EL3_SysRegRead_098fd5c15cd15cd8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg AMAIR_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCFGR_EL0_SysRegRead_ec6dd3c706fcda64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
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
                  else (X_set t 64 (__get_AMCFGR_EL0 (← readReg AMCFGR_EL0)))))))
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
                  else (X_set t 64 (__get_AMCFGR_EL0 (← readReg AMCFGR_EL0))))))
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
                  else (X_set t 64 (__get_AMCFGR_EL0 (← readReg AMCFGR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMCFGR_EL0 (← readReg AMCFGR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCG1IDR_EL0_SysRegRead_0dbcfa52be452f1c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
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
                  else (X_set t 64 (__get_AMCG1IDR_EL0 (← readReg AMCG1IDR_EL0)))))))
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
                  else (X_set t 64 (__get_AMCG1IDR_EL0 (← readReg AMCG1IDR_EL0))))))
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
                  else (X_set t 64 (__get_AMCG1IDR_EL0 (← readReg AMCG1IDR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMCG1IDR_EL0 (← readReg AMCG1IDR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCGCR_EL0_SysRegRead_06267c37ea5fd2cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
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
                  else (X_set t 64 (__get_AMCGCR_EL0 (← readReg AMCGCR_EL0)))))))
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
                  else (X_set t 64 (__get_AMCGCR_EL0 (← readReg AMCGCR_EL0))))))
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
                  else (X_set t 64 (__get_AMCGCR_EL0 (← readReg AMCGCR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMCGCR_EL0 (← readReg AMCGCR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCNTENCLR0_EL0_SysRegRead_21074600beb00df2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMCNTEN0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMCNTEN0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_AMCNTENCLR0_EL0 (← readReg AMCNTENCLR0_EL0))))))))
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
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_AMCNTENCLR0_EL0 (← readReg AMCNTENCLR0_EL0)))))))
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
                  else (X_set t 64 (__get_AMCNTENCLR0_EL0 (← readReg AMCNTENCLR0_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMCNTENCLR0_EL0 (← readReg AMCNTENCLR0_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCNTENCLR1_EL0_SysRegRead_4cb38b40de21160e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMCNTEN1 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMCNTEN1 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_AMCNTENCLR1_EL0 (← readReg AMCNTENCLR1_EL0))))))))
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
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_AMCNTENCLR1_EL0 (← readReg AMCNTENCLR1_EL0)))))))
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
                  else (X_set t 64 (__get_AMCNTENCLR1_EL0 (← readReg AMCNTENCLR1_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMCNTENCLR1_EL0 (← readReg AMCNTENCLR1_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCNTENSET0_EL0_SysRegRead_df359e5215fe4ea4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMCNTEN0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMCNTEN0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_AMCNTENSET0_EL0 (← readReg AMCNTENSET0_EL0))))))))
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
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_AMCNTENSET0_EL0 (← readReg AMCNTENSET0_EL0)))))))
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
                  else (X_set t 64 (__get_AMCNTENSET0_EL0 (← readReg AMCNTENSET0_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMCNTENSET0_EL0 (← readReg AMCNTENSET0_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCNTENSET1_EL0_SysRegRead_d259e0efa9006177 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMCNTEN1 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMCNTEN1 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_AMCNTENSET1_EL0 (← readReg AMCNTENSET1_EL0))))))))
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
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_AMCNTENSET1_EL0 (← readReg AMCNTENSET1_EL0)))))))
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
                  else (X_set t 64 (__get_AMCNTENSET1_EL0 (← readReg AMCNTENSET1_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMCNTENSET1_EL0 (← readReg AMCNTENSET1_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCR_EL0_SysRegRead_fe2573ba12b8cf16 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
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
                  else (X_set t 64 (__get_AMCR_EL0 (← readReg AMCR_EL0)))))))
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
                  else (X_set t 64 (__get_AMCR_EL0 (← readReg AMCR_EL0))))))
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
                  else (X_set t 64 (__get_AMCR_EL0 (← readReg AMCR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMCR_EL0 (← readReg AMCR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegRead_a4167a2ccc34a8ca (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR00_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR00_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR00_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (AMEVCNTR0_EL0_read 0))))))))
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
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR00_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (AMEVCNTR0_EL0_read 0)))))))
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
                  else (X_set t 64 (← (AMEVCNTR0_EL0_read 0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (AMEVCNTR0_EL0_read 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegRead_cc9416b67c23e421 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR03_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR03_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR03_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (AMEVCNTR0_EL0_read 3))))))))
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
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR03_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (AMEVCNTR0_EL0_read 3)))))))
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
                  else (X_set t 64 (← (AMEVCNTR0_EL0_read 3)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (AMEVCNTR0_EL0_read 3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegRead_d036784f50549cc8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR02_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR02_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR02_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (AMEVCNTR0_EL0_read 2))))))))
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
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR02_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (AMEVCNTR0_EL0_read 2)))))))
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
                  else (X_set t 64 (← (AMEVCNTR0_EL0_read 2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (AMEVCNTR0_EL0_read 2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegRead_f7357452cbdf2767 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR01_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR01_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR01_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (AMEVCNTR0_EL0_read 1))))))))
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
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR01_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (AMEVCNTR0_EL0_read 1)))))))
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
                  else (X_set t 64 (← (AMEVCNTR0_EL0_read 1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (AMEVCNTR0_EL0_read 1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_0ca7d1c44e1352f0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR10_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR10_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 0))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR10_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 0))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR10_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 0)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 0)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 0))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_11d34f68d6780256 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR15_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR15_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 5))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR15_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 5))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR15_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 5)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 5)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 5))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_270554ed1cad7329 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR115_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR115_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 15))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR115_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 15))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR115_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 15)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 15)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 15))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_34297951a57ea0ef (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR18_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR18_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 8))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR18_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 8))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR18_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 8)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 8)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 8))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_4784c0c277b5428d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR13_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR13_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 3))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR13_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 3))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR13_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 3)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 3)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 3))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_55e8473fc6bbc0d9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR113_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR113_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 13))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR113_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 13))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR113_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 13)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 13)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 13))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_7638ccb047de09f8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR11_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR11_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR11_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 1))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR11_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 1)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 1)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 1))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_8db93fe7c2515bf5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR14_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR14_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 4))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR14_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 4))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR14_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 4)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 4)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 4))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_9f7317df01644a85 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR111_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR111_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 11))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR111_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 11))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR111_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 11)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 11)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 11))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_bad34f14bd2fb39c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR12_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR12_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR12_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 2))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR12_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 2)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 2)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 2))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_be6aed1af9b22a58 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR110_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR110_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 10))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR110_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 10))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR110_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 10)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 10)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 10))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_bf47e913d26baa8e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR112_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR112_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 12))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR112_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 12))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR112_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 12)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 12)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 12))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_c7849b6a9ce28268 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR114_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR114_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 14))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR114_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 14))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR114_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 14)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 14)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 14))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_ca529b74c1d7516d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR19_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR19_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 9))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR19_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 9))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR19_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 9)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 9)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 9))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_e352be1aa751f006 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR16_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR16_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 6))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR16_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 6))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR16_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 6)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 6)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 6))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_fb04d104547be6cf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR17_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR17_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 7))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR17_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 7))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR17_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 7)))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                      else
                        (do
                          if (((! (IsHighestEL (← readReg PSTATE).EL)) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then (X_set t 64 (Zeros (n := 64)))
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 7)))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) 7))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_0058ecc12215fa39 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA00#12) +i (8 *i 0)))))
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF0_EL2) 0))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF0_EL2) 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_0efd385ac3f50aa7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_32a7e4332477435d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_48d575ae64c47181 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_5616d16017b0ebad (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA00#12) +i (8 *i 3)))))
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF0_EL2) 3))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF0_EL2) 3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_6fb8f8a119c2917d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_8025c4d237ad3c30 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_906fb8ee06808f75 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_90b97336851e0b89 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_9967025452c01cd2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_9b9b8289286b389f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_9c52ba86b79d6d1b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_bc26fe69d64e9fcd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_e7b800151f349b69 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA00#12) +i (8 *i 2)))))
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF0_EL2) 2))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF0_EL2) 2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_fa89039688bc4bb9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_fab3ea7a2072d326 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_AMVOFFEN ← (( do (pure (_get_SCR_EL3_Type_AMVOFFEN (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_14a05140a99b1d6a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 11)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 11))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 11))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_19a0030d7d85728c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 13)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 13))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 13))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_1a9e9a20154e0542 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 8)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 8))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 8))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_20dd4c2724a8f8a0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 7)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 7))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 7))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_36fd38c66709d268 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 10)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 10))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 10))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_42fe0c3a8ef734f0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 1)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 1))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 1))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_5d5ff9d73e486760 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 5)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 5))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 5))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_61ebab1c5fc330a2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 12)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 12))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 12))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_63bf321dec6513c6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 14)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 14))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 14))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_810c9c7ab8f85945 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 4)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 4))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 4))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_89a7234b83ebc6eb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 2)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 2))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 2))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_9ccfe31177eb70bf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 3)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 3))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 3))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_ab60ef2f0cd65aba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 9)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 9))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 9))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_aba56e69378156c9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 6)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 6))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 6))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_bc32b16140cabb5b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 0)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 0))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 0))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegRead_f1c1cecc05c57faa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← (NVMem_read ((BitVec.toNat 0xA80#12) +i (8 *i 15)))))
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
                              else (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 15))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (GetElem?.getElem! (← readReg AMEVCNTVOFF1_EL2) 15))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER0_EL0_SysRegRead_0cc4dde298f89021 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 3)))))))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 3))))))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 3)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER0_EL0_SysRegRead_109f5242c6f95a4b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 0)))))))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 0))))))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER0_EL0_SysRegRead_141bbfd1d5e601d1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 1)))))))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 1))))))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER0_EL0_SysRegRead_4f032bbf168e91d3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 2)))))))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 2))))))
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
                  else (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMEVTYPER0_EL0 (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_02ccdb3991a6241f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER110_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER110_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 10))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER110_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 10))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER110_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 10)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 10)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 10)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_04bf025f6505940b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER12_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER12_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER12_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 2))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER12_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 2)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 2)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 2)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_130fc21a65e30919 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER13_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER13_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 3))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER13_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 3))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER13_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 3)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 3)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 3)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_378b824787ad2fa8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER114_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER114_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 14))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER114_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 14))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER114_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 14)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 14)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 14)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_4517fc1a9af5a349 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER115_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER115_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 15))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER115_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 15))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER115_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 15)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 15)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 15)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_4a0a6a309cab0296 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER16_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER16_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 6))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER16_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 6))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER16_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 6)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 6)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 6)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_50f740f5417b3e8c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER11_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER11_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER11_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 1))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER11_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 1)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 1)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 1)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_9fc9c2c315f2eddc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER112_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER112_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 12))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER112_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 12))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER112_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 12)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 12)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 12)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_a53d76115c4ce8dd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER18_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER18_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 8))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER18_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 8))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER18_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 8)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 8)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 8)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_ace2a16645ca5a01 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER113_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER113_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 13))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER113_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 13))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER113_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 13)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 13)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 13)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_b184c6ea62674df7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER10_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER10_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 0))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER10_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 0))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER10_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 0)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 0)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 0)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_b19d7fec0ca1e05a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER15_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER15_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 5))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER15_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 5))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER15_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 5)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 5)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 5)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_b5481b68c98a55a0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER14_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER14_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 4))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER14_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 4))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER14_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 4)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 4)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 4)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_c06031c8baa68012 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER111_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER111_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 11))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER111_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 11))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER111_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 11)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 11)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 11)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_c8256ab91500d7f3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER17_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER17_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 7))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER17_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 7))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER17_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 7)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 7)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 7)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_d44d986d5aa5ac28 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER19_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER19_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 9))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((← (EL2Enabled ())) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER19_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 9))))))))
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
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER19_EL0 == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 9)))))))
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
                      else (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 9)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) 9)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMUSERENR_EL0_SysRegRead_72607d8d9c634200 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
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
              else (X_set t 64 (__get_AMUSERENR_EL0 (← readReg AMUSERENR_EL0))))))
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
                  else (X_set t 64 (__get_AMUSERENR_EL0 (← readReg AMUSERENR_EL0))))))
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
                  else (X_set t 64 (__get_AMUSERENR_EL0 (← readReg AMUSERENR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_AMUSERENR_EL0 (← readReg AMUSERENR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APDAKeyHi_EL1_SysRegRead_6f8bf97afb0e465f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_APDAKey ← (( do (pure (_get_HFGRTR_EL2_Type_APDAKey (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_APDAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg APDAKeyHi_EL1))))))
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
                  else (X_set t 64 (← readReg APDAKeyHi_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg APDAKeyHi_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APDAKeyLo_EL1_SysRegRead_da997907626beb36 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_APDAKey ← (( do (pure (_get_HFGRTR_EL2_Type_APDAKey (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_APDAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg APDAKeyLo_EL1))))))
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
                  else (X_set t 64 (← readReg APDAKeyLo_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg APDAKeyLo_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APDBKeyHi_EL1_SysRegRead_e38d9de67a6082a7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_APDBKey ← (( do (pure (_get_HFGRTR_EL2_Type_APDBKey (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_APDBKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg APDBKeyHi_EL1))))))
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
                  else (X_set t 64 (← readReg APDBKeyHi_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg APDBKeyHi_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APDBKeyLo_EL1_SysRegRead_d57fe909b886c0fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_APDBKey ← (( do (pure (_get_HFGRTR_EL2_Type_APDBKey (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_APDBKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg APDBKeyLo_EL1))))))
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
                  else (X_set t 64 (← readReg APDBKeyLo_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg APDBKeyLo_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APGAKeyHi_EL1_SysRegRead_0a5b468704a60aab (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_APGAKey ← (( do (pure (_get_HFGRTR_EL2_Type_APGAKey (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_APGAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg APGAKeyHi_EL1))))))
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
                  else (X_set t 64 (← readReg APGAKeyHi_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg APGAKeyHi_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APGAKeyLo_EL1_SysRegRead_b90c447e3bdb3387 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_APGAKey ← (( do (pure (_get_HFGRTR_EL2_Type_APGAKey (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_APGAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg APGAKeyLo_EL1))))))
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
                  else (X_set t 64 (← readReg APGAKeyLo_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg APGAKeyLo_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APIAKeyHi_EL1_SysRegRead_369091161dd81da7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_APIAKey ← (( do (pure (_get_HFGRTR_EL2_Type_APIAKey (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_APIAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg APIAKeyHi_EL1))))))
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
                  else (X_set t 64 (← readReg APIAKeyHi_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg APIAKeyHi_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APIAKeyLo_EL1_SysRegRead_7d4296cd57d27a5d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_APIAKey ← (( do (pure (_get_HFGRTR_EL2_Type_APIAKey (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_APIAKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg APIAKeyLo_EL1))))))
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
                  else (X_set t 64 (← readReg APIAKeyLo_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg APIAKeyLo_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APIBKeyHi_EL1_SysRegRead_8d14ffa361259fa2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_APIBKey ← (( do (pure (_get_HFGRTR_EL2_Type_APIBKey (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_APIBKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg APIBKeyHi_EL1))))))
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
                  else (X_set t 64 (← readReg APIBKeyHi_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg APIBKeyHi_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def APIBKeyLo_EL1_SysRegRead_c29446436810902b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_APK ← (( do (pure (_get_SCR_EL3_Type_APK (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_APK ← (( do (pure (_get_HCR_EL2_Type_APK (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_APIBKey ← (( do (pure (_get_HFGRTR_EL2_Type_APIBKey (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_APIBKey == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_APK == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg APIBKeyLo_EL1))))))
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
                  else (X_set t 64 (← readReg APIBKeyLo_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg APIBKeyLo_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBCR_EL1_SysRegRead_e8e220b931609fe8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x8E0#12))))
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
                              else (X_set t 64 (__get_BRBCR_EL1 (← readReg BRBCR_EL1)))))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_BRBCR_EL1 (← readReg BRBCR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBCR_EL2_SysRegRead_3e399240c4f4d549 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBCTL ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBCTL (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBCTL == 0#1)) : Bool)
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
                              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x8E0#12))))
                              else (X_set t 64 (__get_BRBCR_EL1 (← readReg BRBCR_EL1)))))))))
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
                              then (X_set t 64 (__get_BRBCR_EL2 (← readReg BRBCR_EL2)))
                              else (X_set t 64 (__get_BRBCR_EL1 (← readReg BRBCR_EL1))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_BRBCR_EL1 (← readReg BRBCR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBCR_EL2_SysRegRead_7a9e81b09ce79591 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          else (X_set t 64 (__get_BRBCR_EL2 (← readReg BRBCR_EL2)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_BRBCR_EL2 (← readReg BRBCR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBFCR_EL1_SysRegRead_6dce71f1750cf1d1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBCTL ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBCTL (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBCTL == 0#1)) : Bool)
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
                          else (X_set t 64 (__get_BRBFCR_EL1 (← readReg BRBFCR_EL1))))))))
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
                          else (X_set t 64 (__get_BRBFCR_EL1 (← readReg BRBFCR_EL1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_BRBFCR_EL1 (← readReg BRBFCR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBIDR0_EL1_SysRegRead_4134441fa4c3f5c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBIDR ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBIDR (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBIDR == 0#1)) : Bool)
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
                          else (X_set t 64 (__get_BRBIDR0_EL1 (← readReg BRBIDR0_EL1))))))))
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
                          else (X_set t 64 (__get_BRBIDR0_EL1 (← readReg BRBIDR0_EL1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_BRBIDR0_EL1 (← readReg BRBIDR0_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINFINJ_EL1_SysRegRead_7c147e54f4ecbf52 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else (X_set t 64 (__get_BRBINFINJ_EL1 (← readReg BRBINFINJ_EL1))))))))
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
                          else (X_set t 64 (__get_BRBINFINJ_EL1 (← readReg BRBINFINJ_EL1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_BRBINFINJ_EL1 (← readReg BRBINFINJ_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_004189f53be4d3aa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((26 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 26)))))))))
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
                              if (((26 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 26))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((26 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 26))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_059543eab5e966b1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((16 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 16)))))))))
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
                              if (((16 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 16))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((16 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 16))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_06cfcedba145d8be (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((1 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 1)))))))))
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
                              if (((1 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 1))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((1 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_0b0a91ffc847ffa1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((6 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 6)))))))))
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
                              if (((6 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 6))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((6 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 6))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_0dff5d276a18ac1b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((10 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 10)))))))))
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
                              if (((10 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 10))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((10 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 10))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_1238ef792e876294 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((14 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 14)))))))))
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
                              if (((14 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 14))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((14 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 14))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_12a374a1337f2158 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((27 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 27)))))))))
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
                              if (((27 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 27))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((27 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 27))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_167b0f9ad00f744c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 18)))))))))
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
                              if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 18))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 18))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_2c600906402c2b67 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((8 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 8)))))))))
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
                              if (((8 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 8))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((8 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 8))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_48bbd285cc41ccf1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((4 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 4)))))))))
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
                              if (((4 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 4))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((4 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 4))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_4ae3373d3e11ea10 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((29 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 29)))))))))
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
                              if (((29 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 29))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((29 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 29))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_5328c51266b81007 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((12 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 12)))))))))
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
                              if (((12 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 12))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((12 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 12))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_5d1dd861f0ff77ac (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((9 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 9)))))))))
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
                              if (((9 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 9))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((9 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 9))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_68f733837a85950e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((30 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 30)))))))))
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
                              if (((30 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 30))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((30 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 30))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_6c58e23173be8c63 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((24 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 24)))))))))
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
                              if (((24 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 24))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((24 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 24))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_76723f8ffeba3316 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 19)))))))))
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
                              if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 19))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 19))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_923e32fe7fade07e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((5 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 5)))))))))
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
                              if (((5 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 5))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((5 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 5))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_956d322b1e39b0ab (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((25 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 25)))))))))
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
                              if (((25 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 25))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((25 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 25))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_97b6117930948ca0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((23 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 23)))))))))
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
                              if (((23 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 23))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((23 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 23))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_a11664a8ed6f4106 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((13 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 13)))))))))
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
                              if (((13 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 13))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((13 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 13))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_b4a0ffb7768f7021 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((20 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 20)))))))))
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
                              if (((20 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 20))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((20 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 20))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_ca6fd21020d85edf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((17 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 17)))))))))
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
                              if (((17 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 17))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((17 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 17))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_cd25feee447def98 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((15 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 15)))))))))
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
                              if (((15 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 15))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((15 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 15))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_d0c46fd015ceb879 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((11 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 11)))))))))
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
                              if (((11 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 11))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((11 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 11))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_d553e16381f68050 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((21 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 21)))))))))
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
                              if (((21 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 21))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((21 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 21))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_d6c042d579aad6ae (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((7 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 7)))))))))
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
                              if (((7 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 7))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((7 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 7))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_e899a449a42d0451 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 2)))))))))
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
                              if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 2))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_ea333ab47e4a6f1e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 28)))))))))
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
                              if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 28))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 28))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_ecdadc5359d94302 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 0)))))))))
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
                              if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 0))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_f0d2234cd65ac731 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((22 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 22)))))))))
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
                              if (((22 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 22))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((22 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 22))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_f4230c6e2734deb4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((3 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 3)))))))))
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
                              if (((3 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 3))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((3 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 3))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_f576b69cab3c9e91 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 31)))))))))
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
                              if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 31))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! (← readReg BRBINF_EL1) 31))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRCINJ_EL1_SysRegRead_f235ffd98eed1805 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else (X_set t 64 (← readReg BRBSRCINJ_EL1)))))))
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
                          else (X_set t 64 (← readReg BRBSRCINJ_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg BRBSRCINJ_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_0343a6528d6efd4c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((7 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 7))))))))
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
                              if (((7 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 7)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((7 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 7)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_0b650e0ab6d1b44c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((21 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 21))))))))
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
                              if (((21 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 21)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((21 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 21)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_1c94f14d1fd6245f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((20 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 20))))))))
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
                              if (((20 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 20)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((20 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 20)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_1ffd06111e3a6e95 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((22 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 22))))))))
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
                              if (((22 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 22)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((22 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 22)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_2ff088f1ef08febc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((23 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 23))))))))
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
                              if (((23 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 23)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((23 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 23)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_33c4b2eee9151575 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                              if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 31))))))))
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
                              if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 31)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 31)))
              else (pure ()))))


