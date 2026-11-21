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
def OSDTRTX_EL1_SysRegRead_9df6f1b9434b173d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
      then (X_set t 64 (__get_OSDTRTX_EL1 (← readReg OSDTRTX_EL1)))
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
                                  else (X_set t 64 (__get_OSDTRTX_EL1 (← readReg OSDTRTX_EL1)))))))))
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
                              else (X_set t 64 (__get_OSDTRTX_EL1 (← readReg OSDTRTX_EL1)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_OSDTRTX_EL1 (← readReg OSDTRTX_EL1)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def OSECCR_EL1_SysRegRead_2b476cb67a617cfe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_OSECCR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_OSECCR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __OSLSR_EL1_OSLK ← (( do (pure (_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_OSECCR_EL1 == 1#1)) : Bool)
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
                          if ((__OSLSR_EL1_OSLK == 0#1) : Bool)
                          then (X_set t 64 (← (__UNKNOWN_bits 64)))
                          else (X_set t 64 (__get_OSECCR_EL1 (← readReg OSECCR_EL1))))))))
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
                      if ((__OSLSR_EL1_OSLK == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_OSECCR_EL1 (← readReg OSECCR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__OSLSR_EL1_OSLK == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_OSECCR_EL1 (← readReg OSECCR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def OSLSR_EL1_SysRegRead_ee8639dd7aebdefe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDOSA ← (( do (pure (_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_OSLSR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_OSLSR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_OSLSR_EL1 == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_OSLSR_EL1 (← readReg OSLSR_EL1)))))))
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
                  else (X_set t 64 (__get_OSLSR_EL1 (← readReg OSLSR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_OSLSR_EL1 (← readReg OSLSR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PAN_SysRegRead_ffa7ce033244778f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (((Zeros (n := 41)) +++ (← readReg PSTATE).PAN) +++ (Zeros (n := 22))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (((Zeros (n := 41)) +++ (← readReg PSTATE).PAN) +++ (Zeros (n := 22))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (((Zeros (n := 41)) +++ (← readReg PSTATE).PAN) +++ (Zeros (n := 22))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PAR_EL1_SysRegRead_8d8d0b85bc9f516c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_PAR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_PAR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_PAR_EL1 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (Sail.BitVec.extractLsb (__get_PAR_EL1 (← (PAR_EL1_read ()))) 63 0)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (Sail.BitVec.extractLsb (__get_PAR_EL1 (← (PAR_EL1_read ()))) 63 0))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (Sail.BitVec.extractLsb (__get_PAR_EL1 (← (PAR_EL1_read ()))) 63 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PFAR_EL1_SysRegRead_648f6bc41e720a7a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x2D0#12))))
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
              then (X_set t 64 (__get_PFAR_EL1 (← readReg PFAR_EL1)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_PFAR_EL1 (← readReg PFAR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PFAR_EL1_SysRegRead_edf49fc5ee95c8c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR2_EL2_nPFAR_EL1 ← (( do (pure (_get_HFGRTR2_EL2_Type_nPFAR_EL1 (← readReg HFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (IsFeatureImplemented FEAT_FGT2)))) && (__HFGRTR2_EL2_nPFAR_EL1 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x2D0#12))))
                  else (X_set t 64 (__get_PFAR_EL1 (← readReg PFAR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (__get_PFAR_EL2 (← readReg PFAR_EL2)))
              else (X_set t 64 (__get_PFAR_EL1 (← readReg PFAR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PFAR_EL1 (← readReg PFAR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PFAR_EL2_SysRegRead_b491a80fcabf31ea (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_PFAR_EL2 (← readReg PFAR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PFAR_EL2 (← readReg PFAR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PIRE0_EL1_SysRegRead_1431908c1f187dd9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x290#12))))
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
                      else (X_set t 64 (← readReg PIRE0_EL1))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg PIRE0_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PIRE0_EL2_SysRegRead_77b4d92b42d1e381 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x298#12))))
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
                  else (X_set t 64 (← readReg PIRE0_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PIRE0_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PIRE0_EL2_SysRegRead_9885888a54ddcb18 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_PIEn ← (( do (pure (_get_SCR_EL3_Type_PIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nPIRE0_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nPIRE0_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nPIRE0_EL1 == 0#1)) : Bool)
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
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x290#12))))
                          else (X_set t 64 (← readReg PIRE0_EL1)))))))
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
                      then (X_set t 64 (← readReg PIRE0_EL2))
                      else (X_set t 64 (← readReg PIRE0_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PIRE0_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PIR_EL1_SysRegRead_9dc8ce566aa0dbe0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_PIEn ← (( do (pure (_get_SCR_EL3_Type_PIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nPIR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nPIR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nPIR_EL1 == 0#1)) : Bool)
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
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x2A0#12))))
                          else (X_set t 64 (← readReg PIR_EL1)))))))
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
                      then (X_set t 64 (← readReg PIR_EL2))
                      else (X_set t 64 (← readReg PIR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PIR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PIR_EL1_SysRegRead_d6ac17cfc2f564cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x2A0#12))))
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
                      else (X_set t 64 (← readReg PIR_EL1))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg PIR_EL1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PIR_EL2_SysRegRead_e7b38688c081b516 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else (X_set t 64 (← readReg PIR_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PIR_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PIR_EL3_SysRegRead_1dc2ca24d5a22e66 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (← readReg PIR_EL3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMBIDR_EL1_SysRegRead_48dfa0662916d0ce (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMBIDR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMBIDR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMBIDR_EL1 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_PMBIDR_EL1 (← readReg PMBIDR_EL1))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_PMBIDR_EL1 (← readReg PMBIDR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMBIDR_EL1 (← readReg PMBIDR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMBLIMITR_EL1_SysRegRead_698047bfa5d212f3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMBLIMITR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMBLIMITR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_E2PB ← (( do (pure (_get_MDCR_EL2_Type_E2PB (← readReg MDCR_EL2))) ) : SailM (BitVec 2) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMBLIMITR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (let b__0 := __MDCR_EL2_E2PB
                       if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                       then true
                       else false : Bool)) : Bool)
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
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x800#12))))
                          else (X_set t 64 (__get_PMBLIMITR_EL1 (← readReg PMBLIMITR_EL1))))))))
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
                  else (X_set t 64 (__get_PMBLIMITR_EL1 (← readReg PMBLIMITR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMBLIMITR_EL1 (← readReg PMBLIMITR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMBPTR_EL1_SysRegRead_fecbe9ae2e92d802 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMBPTR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMBPTR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_E2PB ← (( do (pure (_get_MDCR_EL2_Type_E2PB (← readReg MDCR_EL2))) ) : SailM (BitVec 2) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMBPTR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (let b__0 := __MDCR_EL2_E2PB
                       if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                       then true
                       else false : Bool)) : Bool)
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
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x810#12))))
                          else (X_set t 64 (← readReg PMBPTR_EL1)))))))
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
                  else (X_set t 64 (← readReg PMBPTR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PMBPTR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMBSR_EL1_SysRegRead_65583fd5eecf376d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMBSR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMBSR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_E2PB ← (( do (pure (_get_MDCR_EL2_Type_E2PB (← readReg MDCR_EL2))) ) : SailM (BitVec 2) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMBSR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (let b__0 := __MDCR_EL2_E2PB
                       if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
                       then true
                       else false : Bool)) : Bool)
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
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x820#12))))
                          else (X_set t 64 (__get_PMBSR_EL1 (← readReg PMBSR_EL1))))))))
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
                  else (X_set t 64 (__get_PMBSR_EL1 (← readReg PMBSR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMBSR_EL1 (← readReg PMBSR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCCFILTR_EL0_SysRegRead_5ac92cf4fcc5c832 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMCCFILTR_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMCCFILTR_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCCFILTR_EL0 == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMCCFILTR_EL0 (← readReg PMCCFILTR_EL0))))))))
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCCFILTR_EL0 == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMCCFILTR_EL0 (← readReg PMCCFILTR_EL0)))))))
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
                  else (X_set t 64 (__get_PMCCFILTR_EL0 (← readReg PMCCFILTR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMCCFILTR_EL0 (← readReg PMCCFILTR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCCNTR_EL0_SysRegRead_ec496c5d54ab7b85 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMCCNTR_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMCCNTR_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((IsFeatureImplemented FEAT_PMUv3p9) <&&> (do
               (pure (((_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0)) +++ ((_get_PMUSERENR_EL0_Type_CR (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)))) == 0b000#3))) <||> (do
               (pure (! (← (IsFeatureImplemented FEAT_PMUv3p9)))) <&&> (do
                 (pure (((_get_PMUSERENR_EL0_Type_CR (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) == 0b00#2)))))) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCCNTR_EL0 == 1#1)) : Bool)
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
                      else (X_set t 64 (← readReg PMCCNTR_EL0)))))))
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCCNTR_EL0 == 1#1)) : Bool)
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
                      else (X_set t 64 (← readReg PMCCNTR_EL0))))))
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
                  else (X_set t 64 (← readReg PMCCNTR_EL0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PMCCNTR_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCCNTSVR_EL1_SysRegRead_1c4e4329b1d511c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg PMCCNTSVR_EL1))))))
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
                  else (X_set t 64 (← readReg PMCCNTSVR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PMCCNTSVR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCEID0_EL0_SysRegRead_f2e86782f8f3f9b7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_TID ← (( do (pure (_get_PMUSERENR_EL0_Type_TID (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMCEIDn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMCEIDn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
              if (((← (IsFeatureImplemented FEAT_PMUv3p9)) && (__PMUSERENR_EL0_TID == 1#1)) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCEIDn_EL0 == 1#1)) : Bool)
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
                          else (X_set t 64 (← readReg PMCEID0_EL0))))))))
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCEIDn_EL0 == 1#1)) : Bool)
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
                      else (X_set t 64 (← readReg PMCEID0_EL0))))))
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
                  else (X_set t 64 (← readReg PMCEID0_EL0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PMCEID0_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCEID1_EL0_SysRegRead_88fe472f132d5d45 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_TID ← (( do (pure (_get_PMUSERENR_EL0_Type_TID (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMCEIDn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMCEIDn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
              if (((← (IsFeatureImplemented FEAT_PMUv3p9)) && (__PMUSERENR_EL0_TID == 1#1)) : Bool)
              then
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCEIDn_EL0 == 1#1)) : Bool)
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
                          else (X_set t 64 (← readReg PMCEID1_EL0))))))))
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCEIDn_EL0 == 1#1)) : Bool)
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
                      else (X_set t 64 (← readReg PMCEID1_EL0))))))
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
                  else (X_set t 64 (← readReg PMCEID1_EL0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PMCEID1_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCNTENCLR_EL0_SysRegRead_9c63b37a1be89728 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMCNTEN ← (( do (pure (_get_HDFGRTR_EL2_Type_PMCNTEN (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCNTEN == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMCNTENCLR_EL0 (← readReg PMCNTENCLR_EL0))))))))
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCNTEN == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMCNTENCLR_EL0 (← readReg PMCNTENCLR_EL0)))))))
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
                  else (X_set t 64 (__get_PMCNTENCLR_EL0 (← readReg PMCNTENCLR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMCNTENCLR_EL0 (← readReg PMCNTENCLR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCNTENSET_EL0_SysRegRead_4d90af887d9c8c94 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMCNTEN ← (( do (pure (_get_HDFGRTR_EL2_Type_PMCNTEN (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCNTEN == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMCNTENSET_EL0 (← readReg PMCNTENSET_EL0))))))))
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCNTEN == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMCNTENSET_EL0 (← readReg PMCNTENSET_EL0)))))))
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
                  else (X_set t 64 (__get_PMCNTENSET_EL0 (← readReg PMCNTENSET_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMCNTENSET_EL0 (← readReg PMCNTENSET_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCR_EL0_SysRegRead_e26571c3d63ff1ee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPMCR ← (( do (pure (_get_MDCR_EL2_Type_TPMCR (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((IsFeatureImplemented FEAT_PMUv3p9) <&&> (do
               (pure (((_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) != 0b01#2))) <||> (do
               (pure ((! (← (IsFeatureImplemented FEAT_PMUv3p9))) && (__PMUSERENR_EL0_EN == 0#1)))))) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__MDCR_EL2_TPMCR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (__get_PMCR_EL0 (← readReg PMCR_EL0)))))))))
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
              if (((← (EL2Enabled ())) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__MDCR_EL2_TPMCR == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← (__get_PMCR_EL0 (← readReg PMCR_EL0))))))))
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
                  else (X_set t 64 (← (__get_PMCR_EL0 (← readReg PMCR_EL0))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (__get_PMCR_EL0 (← readReg PMCR_EL0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMECR_EL1_SysRegRead_701363aef834edcc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMECR_EL1 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMECR_EL1 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMECR_EL1 == 0#1)) : Bool)
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
                                  else (X_set t 64 (__get_PMECR_EL1 (← readReg PMECR_EL1))))))))))
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
                          else (X_set t 64 (__get_PMECR_EL1 (← readReg PMECR_EL1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMECR_EL1 (← readReg PMECR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_0593376102dfa06d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (10 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 10))))))))
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
                           (pure (10 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 10)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 10))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 10))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_0d3db5f733fce750 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (15 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 15))))))))
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
                           (pure (15 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 15)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 15))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 15))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_0fa6d9f54f3566c9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (5 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 5))))))))
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
                           (pure (5 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 5)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 5))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 5))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_10f19f05478e0298 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (8 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 8))))))))
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
                           (pure (8 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 8)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 8))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 8))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_1182d540f254acac (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (12 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 12))))))))
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
                           (pure (12 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 12)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 12))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 12))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_1ab539f73d82d8d9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (6 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 6))))))))
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
                           (pure (6 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 6)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 6))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 6))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_2a52665b668ba6a3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (7 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 7))))))))
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
                           (pure (7 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 7)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 7))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 7))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_2f26e246b6e98799 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (2 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 2))))))))
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
                           (pure (2 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 2)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_3152dcccddae7402 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (3 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 3))))))))
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
                           (pure (3 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 3)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 3))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_32b4fcb392e5c312 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (29 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 29))))))))
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
                           (pure (29 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 29)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 29))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 29))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_3cf749b2a6f0d8e8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (13 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 13))))))))
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
                           (pure (13 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 13)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 13))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 13))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_3fd74d86919a41a5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (19 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 19))))))))
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
                           (pure (19 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 19)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 19))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 19))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_53822901bce95688 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (28 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 28))))))))
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
                           (pure (28 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 28)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 28))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 28))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_593e15d8d87f3370 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (27 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 27))))))))
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
                           (pure (27 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 27)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 27))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 27))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_693e4ccc8252a9a7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (18 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 18))))))))
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
                           (pure (18 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 18)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 18))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 18))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_6b9b795fff65a19d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (20 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 20))))))))
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
                           (pure (20 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 20)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 20))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 20))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_6d59e307d3cd7a1c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (23 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 23))))))))
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
                           (pure (23 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 23)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 23))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 23))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_6eef6c9d0ea660a1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (26 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 26))))))))
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
                           (pure (26 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 26)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 26))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 26))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_73ed225f0812fbfc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (16 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 16))))))))
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
                           (pure (16 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 16)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 16))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 16))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_748d6e2e7bd869de (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (22 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 22))))))))
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
                           (pure (22 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 22)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 22))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 22))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_776dc50ca01e0285 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (4 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 4))))))))
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
                           (pure (4 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 4)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 4))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 4))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_81c5bd2bbc23b640 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (1 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 1))))))))
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
                           (pure (1 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 1)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_a360f253ceba1de0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (9 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 9))))))))
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
                           (pure (9 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 9)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 9))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 9))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_bddfd936634ddadc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (24 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 24))))))))
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
                           (pure (24 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 24)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 24))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 24))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_c3ba32793ae88442 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (14 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 14))))))))
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
                           (pure (14 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 14)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 14))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 14))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_ca58b1e5989f1015 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (11 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 11))))))))
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
                           (pure (11 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 11)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 11))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 11))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_e23b48b5ac325a95 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (21 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 21))))))))
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
                           (pure (21 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 21)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 21))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 21))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_e5a283ed2b79bd84 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (30 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 30))))))))
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
                           (pure (30 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 30)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 30))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 30))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_ed4b4b8084b6d41d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (0 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 0))))))))
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
                           (pure (0 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 0)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_ef3a8d2a7921c11c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (17 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 17))))))))
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
                           (pure (17 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 17)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 17))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 17))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_fccbe0710386c98a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (25 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 25))))))))
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
                           (pure (25 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 25)))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 25))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) 25))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_0219fbdb2658ca68 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 26))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 26))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 26))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_10cfea5393e5a113 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 6))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 6))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 6))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_36f90261f51de7a4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 11))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 11))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 11))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_384f3a84fabf1c68 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 8))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 8))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 8))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_3f5ceece7b1ab633 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 12))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 12))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 12))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_4a27b429d70fb026 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 28))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 28))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 28))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_4c97fc2d1ca8cf1e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 25))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 25))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 25))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_5646c848d2870ac9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 15))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 15))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 15))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_59a2849f7eb3b332 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 27))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 27))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 27))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_59dd9f25ebd351ac (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 13))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 13))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 13))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_69c766eb655b6bd8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 17))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 17))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 17))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_7000ac16a0f93cee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 14))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 14))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 14))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_73e30fcdf9fe2edd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 22))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 22))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 22))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_7d149b7cd797530b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 30))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 30))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 30))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_82c544942be55f96 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 24))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 24))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 24))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_8418bd2288f058de (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 16))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 16))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 16))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_93e122dd4e325251 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 2))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_9541923a3ae283ea (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 23))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 23))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 23))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_ad118dbfadee9377 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 7))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 7))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 7))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_b1095a7af5788bf0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 3))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 3))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 3))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_b5f18a055135ef08 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 9))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 9))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 9))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_b7a27d9b684d8f1b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 1))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_bb81ca0d64a32b78 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 10))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 10))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 10))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_c0ae6177773c98b2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 19))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 19))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 19))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_ce304be785bc43da (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 5))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 5))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 5))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_d3fed862ea81087f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 4))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 4))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 4))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_dcb2c17a0373111a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 18))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 18))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 18))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_e9a366e0017307cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 29))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 29))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 29))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_f8609d37ac8354cc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 0))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_f925d17f40acee9c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 21))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 21))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 21))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_fda3561b105a2867 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 20))))))
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
                  else (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 20))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTSVR_EL1) 20))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_073a4fe6d2f5a921 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (13 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 13)))))))))
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
                           (pure (13 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 13))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 13)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 13)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_12c2ea6445066d74 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (6 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 6)))))))))
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
                           (pure (6 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 6))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 6)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 6)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_13c3c0867de835a2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (23 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 23)))))))))
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
                           (pure (23 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 23))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 23)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 23)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_14beb5e8e42eceb3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (14 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 14)))))))))
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
                           (pure (14 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 14))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 14)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 14)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_161a91be0c63b6f4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (18 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 18)))))))))
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
                           (pure (18 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 18))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 18)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 18)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_187174725e559008 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (21 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 21)))))))))
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
                           (pure (21 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 21))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 21)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 21)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_1a04be91449acb40 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (8 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 8)))))))))
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
                           (pure (8 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 8))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 8)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 8)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_1dbe5107f25be020 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (4 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 4)))))))))
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
                           (pure (4 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 4))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 4)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 4)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_1f37321b901f8989 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (10 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 10)))))))))
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
                           (pure (10 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 10))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 10)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 10)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_264c590d45142978 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (5 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 5)))))))))
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
                           (pure (5 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 5))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 5)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 5)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_303aca4655281092 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (0 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 0)))))))))
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
                           (pure (0 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 0))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_3420cbf7b2d038f8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (28 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 28)))))))))
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
                           (pure (28 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 28))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 28)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 28)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_49df7d27e017454d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (3 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 3)))))))))
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
                           (pure (3 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 3))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 3)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_4d7b8571d7d827fa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (12 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 12)))))))))
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
                           (pure (12 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 12))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 12)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 12)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_50be283a37e4fd31 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (11 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 11)))))))))
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
                           (pure (11 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 11))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 11)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 11)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_59df350d04568b64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (7 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 7)))))))))
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
                           (pure (7 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 7))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 7)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 7)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_6096f129eb2ac985 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (16 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 16)))))))))
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
                           (pure (16 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 16))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 16)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 16)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_6f9a48444f4b276b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (29 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 29)))))))))
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
                           (pure (29 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 29))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 29)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 29)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_74117943f83c7293 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (24 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 24)))))))))
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
                           (pure (24 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 24))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 24)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 24)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_82c0bc230c1e3204 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (30 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 30)))))))))
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
                           (pure (30 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 30))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 30)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 30)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_953a504769c668b0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (27 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 27)))))))))
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
                           (pure (27 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 27))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 27)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 27)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_a6915f5d07275c6c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (9 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 9)))))))))
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
                           (pure (9 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 9))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 9)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 9)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_b06bc5007c474af3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (22 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 22)))))))))
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
                           (pure (22 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 22))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 22)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 22)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_b0eea7edf1a1fecf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (1 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 1)))))))))
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
                           (pure (1 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 1))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_b63b7d8fea5e18df (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (20 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 20)))))))))
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
                           (pure (20 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 20))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 20)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 20)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_b777b07a1ab3a531 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (17 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 17)))))))))
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
                           (pure (17 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 17))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 17)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 17)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_c20edd6d6b9803a3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (2 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 2)))))))))
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
                           (pure (2 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 2))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_c8e002b2195e5a12 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (25 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 25)))))))))
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
                           (pure (25 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 25))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 25)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 25)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_c8e92c1375bb4b38 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (19 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 19)))))))))
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
                           (pure (19 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 19))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 19)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 19)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_cd99afc01b24bf2b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (26 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 26)))))))))
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
                           (pure (26 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 26))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 26)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 26)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegRead_d41d3960b7ebf0de (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                           (pure (15 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 15)))))))))
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
                           (pure (15 ≥b (← (AArch64_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 15))))))))
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
                  else (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 15)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMEVTYPER_EL0 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) 15)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMIAR_EL1_SysRegRead_8a45c86d25fdd6b8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMIAR_EL1 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMIAR_EL1 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMIAR_EL1 == 0#1)) : Bool)
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
                                  else (X_set t 64 (← readReg PMIAR_EL1)))))))))
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
                          else (X_set t 64 (← readReg PMIAR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PMIAR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMICFILTR_EL0_SysRegRead_b736a151969b8c3c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_UEN ← (( do (pure (_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMICFILTR_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMICFILTR_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
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
              if ((__PMUSERENR_EL0_UEN == 0#1) : Bool)
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMICFILTR_EL0 == 0#1)) : Bool)
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
                                  else (X_set t 64 (__get_PMICFILTR_EL0 (← readReg PMICFILTR_EL0)))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMICFILTR_EL0 == 0#1)) : Bool)
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
                                  else (X_set t 64 (__get_PMICFILTR_EL0 (← readReg PMICFILTR_EL0))))))))))
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
                          else (X_set t 64 (__get_PMICFILTR_EL0 (← readReg PMICFILTR_EL0)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMICFILTR_EL0 (← readReg PMICFILTR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMICNTR_EL0_SysRegRead_468ebcab1dcb0580 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_UEN ← (( do (pure (_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMICNTR_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMICNTR_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
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
              if ((__PMUSERENR_EL0_UEN == 0#1) : Bool)
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMICNTR_EL0 == 0#1)) : Bool)
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
                                  else (X_set t 64 (← readReg PMICNTR_EL0))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMICNTR_EL0 == 0#1)) : Bool)
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
                                  else (X_set t 64 (← readReg PMICNTR_EL0)))))))))
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
                          else (X_set t 64 (← readReg PMICNTR_EL0))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PMICNTR_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMICNTSVR_EL1_SysRegRead_1ebf8763b2140fc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPMSS ← (( do (pure (_get_MDCR_EL3_Type_EnPMSS (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSSDATA ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSSDATA (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSSDATA == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (← readReg PMICNTSVR_EL1))))))
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
                  else (X_set t 64 (← readReg PMICNTSVR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg PMICNTSVR_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMINTENCLR_EL1_SysRegRead_fb98bdd5aa053775 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMINTEN ← (( do (pure (_get_HDFGRTR_EL2_Type_PMINTEN (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMINTEN == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMINTENCLR_EL1 (← readReg PMINTENCLR_EL1)))))))
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
                  else (X_set t 64 (__get_PMINTENCLR_EL1 (← readReg PMINTENCLR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMINTENCLR_EL1 (← readReg PMINTENCLR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMINTENSET_EL1_SysRegRead_84b31efb21c9f5ab (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMINTEN ← (( do (pure (_get_HDFGRTR_EL2_Type_PMINTEN (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMINTEN == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMINTENSET_EL1 (← readReg PMINTENSET_EL1)))))))
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
                  else (X_set t 64 (__get_PMINTENSET_EL1 (← readReg PMINTENSET_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMINTENSET_EL1 (← readReg PMINTENSET_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMMIR_EL1_SysRegRead_0052425c6ad862e6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMMIR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMMIR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMMIR_EL1 == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMMIR_EL1 (← readReg PMMIR_EL1)))))))
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
                  else (X_set t 64 (__get_PMMIR_EL1 (← readReg PMMIR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMMIR_EL1 (← readReg PMMIR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMOVSCLR_EL0_SysRegRead_c99057064f1c4d43 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMOVS ← (( do (pure (_get_HDFGRTR_EL2_Type_PMOVS (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMOVS == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMOVSCLR_EL0 (← readReg PMOVSCLR_EL0))))))))
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMOVS == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMOVSCLR_EL0 (← readReg PMOVSCLR_EL0)))))))
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
                  else (X_set t 64 (__get_PMOVSCLR_EL0 (← readReg PMOVSCLR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMOVSCLR_EL0 (← readReg PMOVSCLR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMOVSSET_EL0_SysRegRead_6d3f79f9beba4196 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMOVS ← (( do (pure (_get_HDFGRTR_EL2_Type_PMOVS (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMOVS == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMOVSSET_EL0 (← readReg PMOVSSET_EL0))))))))
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMOVS == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMOVSSET_EL0 (← readReg PMOVSSET_EL0)))))))
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
                  else (X_set t 64 (__get_PMOVSSET_EL0 (← readReg PMOVSSET_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMOVSSET_EL0 (← readReg PMOVSSET_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSCR_EL1_SysRegRead_feea919a1dc38dc5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x828#12))))
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
                      else (X_set t 64 (__get_PMSCR_EL1 (← readReg PMSCR_EL1)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_PMSCR_EL1 (← readReg PMSCR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSCR_EL2_SysRegRead_7e9c76511198b62b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
                  else (X_set t 64 (__get_PMSCR_EL2 (← readReg PMSCR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMSCR_EL2 (← readReg PMSCR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSCR_EL2_SysRegRead_feca5252d10f1b6c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMSCR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMSCR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPMS ← (( do (pure (_get_MDCR_EL2_Type_TPMS (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMSCR_EL1 == 1#1)) : Bool)
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
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x828#12))))
                          else (X_set t 64 (__get_PMSCR_EL1 (← readReg PMSCR_EL1))))))))
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
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (__get_PMSCR_EL2 (← readReg PMSCR_EL2)))
                      else (X_set t 64 (__get_PMSCR_EL1 (← readReg PMSCR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMSCR_EL1 (← readReg PMSCR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSDSFR_EL1_SysRegRead_dbabfebdd50e6ad5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPMS3 ← (( do (pure (_get_MDCR_EL3_Type_EnPMS3 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nPMSDSFR_EL1 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nPMSDSFR_EL1 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPMS ← (( do (pure (_get_MDCR_EL2_Type_TPMS (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPMS3 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
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
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nPMSDSFR_EL1 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_TPMS == 1#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_EnPMS3 == 0#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
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
                                      then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x858#12))))
                                      else (X_set t 64 (← (__get_PMSDSFR_EL1 (← readReg PMSDSFR_EL1))))))))))))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPMS3 == 0#1)) : Bool)
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
                          if (((HaveEL EL3) && (__MDCR_EL3_EnPMS3 == 0#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (← (__get_PMSDSFR_EL1 (← readReg PMSDSFR_EL1))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (__get_PMSDSFR_EL1 (← readReg PMSDSFR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSELR_EL0_SysRegRead_597778422a5e1e61 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMSELR_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMSELR_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMSELR_EL0 == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMSELR_EL0 (← readReg PMSELR_EL0))))))))
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMSELR_EL0 == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMSELR_EL0 (← readReg PMSELR_EL0)))))))
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
                  else (X_set t 64 (__get_PMSELR_EL0 (← readReg PMSELR_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMSELR_EL0 (← readReg PMSELR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSEVFR_EL1_SysRegRead_609a095fd2f44185 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMSEVFR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMSEVFR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMSEVFR_EL1 == 1#1)) : Bool)
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
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x830#12))))
                          else (X_set t 64 (← (__get_PMSEVFR_EL1 (← readReg PMSEVFR_EL1)))))))))
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
                  else (X_set t 64 (← (__get_PMSEVFR_EL1 (← readReg PMSEVFR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (__get_PMSEVFR_EL1 (← readReg PMSEVFR_EL1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSFCR_EL1_SysRegRead_6babf00bd8f977b2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_NSPBE ← (( do (pure (_get_MDCR_EL3_Type_NSPBE (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NSE ← (( do (pure (_get_SCR_EL3_Type_NSE (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMSFCR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMSFCR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMSFCR_EL1 == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_PMSFCR_EL1 (← readReg PMSFCR_EL1)))))))
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
                  else (X_set t 64 (__get_PMSFCR_EL1 (← readReg PMSFCR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_PMSFCR_EL1 (← readReg PMSFCR_EL1)))
              else (pure ()))))


