import Armv9.Flow
import Armv9.Prelude
import Armv9.V8Base
import Armv9.Stubs
import Armv9.SysregsAutogen.P04

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

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE2_SysOpsWrite128_cf1b5c7d72a7a1dc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE3IS_SysOpsWrite128_41a3b7f5eb2783af (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE3IS_SysOpsWrite128_436ad5bd6c95d188 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE3OS_SysOpsWrite128_0bd4cb2b344ca9a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE3OS_SysOpsWrite128_7791c494d2ef59ef (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE3_SysOpsWrite128_2fd14fc00c09a0fd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE3_SysOpsWrite128_46537a58be020b54 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE1IS_SysOpsWrite128_b7a50d0df5ca047e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVALE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVALE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLB == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT)) <&&> (do
                             (pure (! (HaveEL EL3))) <||> (do
                               (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVALE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE1IS_SysOpsWrite128_e79fa2efd56cba22 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVALE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVALE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TTLB == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVALE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE1OS_SysOpsWrite128_3cce7186e158fbef (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVALE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVALE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TTLB == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVALE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE1OS_SysOpsWrite128_3dad834e560485db (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVALE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVALE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLB == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT)) <&&> (do
                             (pure (! (HaveEL EL3))) <||> (do
                               (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVALE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE1_SysOpsWrite128_5f40ee04803f7fa0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVALE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVALE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FB ← (( do (pure (_get_HCR_EL2_Type_FB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TTLB == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVALE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE1_SysOpsWrite128_eee3bc60168bedcf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVALE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVALE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FB ← (( do (pure (_get_HCR_EL2_Type_FB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLB == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT)) <&&> (do
                         (pure (! (HaveEL EL3))) <||> (do
                           (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVALE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2IS_SysOpsWrite128_678498d40a585a6e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2IS_SysOpsWrite128_78fde03af9aaffc2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((__HCR_EL2_E2H == 1#1) : Bool)
                          then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2OS_SysOpsWrite128_843e0c96a4c62b9d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2OS_SysOpsWrite128_a461faf4d3b82a3e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((__HCR_EL2_E2H == 1#1) : Bool)
                          then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2_SysOpsWrite128_9b47499d61569e08 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((__HCR_EL2_E2H == 1#1) : Bool)
                          then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2_SysOpsWrite128_ad7af3eba7e26934 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3IS_SysOpsWrite128_c86e34b8232f3903 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3IS_SysOpsWrite128_df84b0484150f9e9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3OS_SysOpsWrite128_e22bb7777364db32 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3OS_SysOpsWrite128_f558b9d9636e92e8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3_SysOpsWrite128_48fc2e32848138c0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((! (← (IsFeatureImplemented FEAT_XS))) : Bool)
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
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3_SysOpsWrite128_da83d084586f123a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def S3_op1_Cn_Cm_op2_SysRegRead_9e206a297d1c5480 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_TIDCP ← (( do (pure (_get_SCTLR_EL1_Type_TIDCP (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_TIDCP ← (( do (pure (_get_SCTLR_EL2_Type_TIDCP (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TIDCP ← (( do (pure (_get_HCR_EL2_Type_TIDCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_TIDCP == 1#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_TIDCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_ImpDefSysRegRead op0 op1 CRn CRm op2 t)))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TIDCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_ImpDefSysRegRead op0 op1 CRn CRm op2 t))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_ImpDefSysRegRead op0 op1 CRn CRm op2 t)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_ImpDefSysRegRead op0 op1 CRn CRm op2 t)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMCFGR_EL1_SysRegRead_3bbfca307eea028a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMID ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMID (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMID == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMCFGR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMCFGR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMCFGR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMCGCR_EL1_SysRegRead_529e10a6261e7d96 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMID ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMID (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMID == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMCGCR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMCGCR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMCGCR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMCNTENCLR_EL0_SysRegRead_1114ed6fac10af30 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMCNTEN ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMCNTEN (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMCNTEN == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMCNTENCLR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMCNTEN == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMCNTENCLR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMCNTENCLR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMCNTENCLR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMCNTENSET_EL0_SysRegRead_d76b56a27ec0166e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMCNTEN ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMCNTEN (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMCNTEN == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMCNTENSET_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMCNTEN == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMCNTENSET_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMCNTENSET_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMCNTENSET_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMCR_EL0_SysRegRead_8d094d8673390ddf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMCR_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMCR_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMCR_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMCR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMCR_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMCR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMCR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMCR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMDEVAFF_EL1_SysRegRead_14639bbf25c1b503 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMDEVAFF_EL1 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMDEVAFF_EL1 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMDEVAFF_EL1 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMDEVAFF_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMDEVAFF_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMDEVAFF_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMDEVARCH_EL1_SysRegRead_f379f5d64ab8b025 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMID ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMID (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMID == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMDEVARCH_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMDEVARCH_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMDEVARCH_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_17c3b03e92e863c8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_21440ea7cf979c85 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_2a5f7477440a0d8c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_2a6f6484aeebace8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_3bbdde355e317836 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_3e60f4578776ee77 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_47746fabe04a4008 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_6629043b009838f2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_678889e62977a375 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_7ed464eec50f477f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_9efab29059e715cc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_ab17ee4b9b9152f9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_ab354cbb8f86428d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_bcfc64cd2c6760f8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_d23e4db3dd4c8878 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegRead_dd0fbaf64169b322 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVCNTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_0f60cc3cb4a8e9b3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_310eb78ca3ffcdd5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_3c202af9a88305f9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_4309271c5c3f50c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_433638c7dd5d7f8c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_51af2efaff004e74 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_53e34bafcb1745bf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_5f57fc70d1c81668 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_811ad3f997f59858 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_a505a5c15b00753c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_b92ce31d6b189d89 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_becf2c3488c0840f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_c26a621e717d6ec0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_d0361acb26713433 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_d72b4e2f828258be (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegRead_dc68673c986189cc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILT2R_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_013cb2536335679a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_2014e793fb76aa0b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_2199824cc2c1b975 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_2f720274e00b27d8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_56d1d9f5e0f84f06 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_67458b6de4d2f083 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_6a3366c40ed33a8b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_87ded94d106ff97e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_8c7e069d9db6465d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_8d4f3607df002a1e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_9b069b7382cb8ace (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_b7b783651f33ef8d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_bdb381032f2d5abe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_c542f9553bc934d3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_ca2e4c8f2660e4c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegRead_d29d0353b14cc20b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14))))))))
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
                  else (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVFILTR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_12d4102729189c27 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_4176d7bf912de1b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_63f86d87692f2f5f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_6b1045c77e27556f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_75ed658b96b65c13 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_833b4e297c71de6a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_957f0f2e2a9b82fd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_99a60c759c66512d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_a31ff8f9d8fc694e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_c0cff22e18b46a65 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_c2de0f8c4622eee8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_e24de41e0c3b53d0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_e7a481429e83f45a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_ec65f2c5c1f0aa41 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegRead_eff783e04019e7d0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
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
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) == 0b00#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) == 0b00#2))))) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) == 0b00#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5)))
              else (pure ()))))


