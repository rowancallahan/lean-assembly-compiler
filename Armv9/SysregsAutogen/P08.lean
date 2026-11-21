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
def TLBI_VALE3IS_SysOpsWrite_4c94c8515b6e4dd8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE3IS_SysOpsWrite_dae432255a8b0524 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE3OS_SysOpsWrite_767bde9c297cce04 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE3OS_SysOpsWrite_af6269968bb4ec2c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE3_SysOpsWrite_6432751b5694bad8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE3_SysOpsWrite_eb6afd5e3f195389 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1IS_SysOpsWrite_8653d883f8306258 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVMALLE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVMALLE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TTLB == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVMALLE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBI_AllAttr)
              else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBI_AllAttr)
                  else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1IS_SysOpsWrite_b92e6f7b045bcd26 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVMALLE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVMALLE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT)) <&&> (do
                             (pure (! (HaveEL EL3))) <||> (do
                               (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVMALLE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBI_ExcludeXS)
                  else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1OS_SysOpsWrite_71ae489ebaf642d0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVMALLE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVMALLE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TTLB == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVMALLE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_AllAttr)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBI_AllAttr)
              else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_AllAttr))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBI_AllAttr)
                  else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_AllAttr))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1OS_SysOpsWrite_9b7b764d81828e24 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVMALLE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVMALLE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT)) <&&> (do
                             (pure (! (HaveEL EL3))) <||> (do
                               (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVMALLE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBI_ExcludeXS)
                  else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1_SysOpsWrite_bcd60b78fb7e2b4a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVMALLE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVMALLE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT)) <&&> (do
                         (pure (! (HaveEL EL3))) <||> (do
                           (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVMALLE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBI_ExcludeXS)
                  else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1_SysOpsWrite_d94c690b16646ffd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVMALLE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVMALLE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVMALLE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBI_AllAttr)
              else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBI_AllAttr)
                  else (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1IS_SysOpsWrite_3dfe7b46e2ce9676 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr)
                  else (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1IS_SysOpsWrite_94de5730f49bdd76 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS)
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1OS_SysOpsWrite_1c9b124b11d1cf42 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_AllAttr)
                  else (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_AllAttr))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1OS_SysOpsWrite_98d1faaee38ba3a7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS)
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1_SysOpsWrite_04d7802e0a5bffbf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr)
                  else (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1_SysOpsWrite_252a42c486a42c51 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS)
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (AArch64_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS)
                      else (AArch64_TLBI_VMALLS12 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def GCSPOPM_SysInstrWithResult_785f34ad5cd557fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (X_set t 64 (← (GCSPOPM ())))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (← (GCSPOPM ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← (GCSPOPM ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (GCSPOPM ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSSS2_SysInstrWithResult_f9ffdfaa333b34bf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (X_set t 64 (← (GCSSS2 ())))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (← (GCSSS2 ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← (GCSSS2 ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (GCSSS2 ())))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegWrite64_00363288e0ffc481 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
           (EL2Enabled ())) <&&> (do
           (pure (! (← (ELUsingAArch32 EL2))))))) && (0 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (ELUsingAArch32 EL2)))) && (0 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
      else
        (do
          if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
          then writeReg AMEVCNTR0 (vectorUpdate (← readReg AMEVCNTR0) 0 (Mk_AMEVCNTR0_Type ((← (R_read t2)) +++ (← (R_read t)))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit)))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegWrite64_125e5d1a241e0a34 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
           (EL2Enabled ())) <&&> (do
           (pure (! (← (ELUsingAArch32 EL2))))))) && (3 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (ELUsingAArch32 EL2)))) && (3 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
      else
        (do
          if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
          then writeReg AMEVCNTR0 (vectorUpdate (← readReg AMEVCNTR0) 3 (Mk_AMEVCNTR0_Type ((← (R_read t2)) +++ (← (R_read t)))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit)))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegWrite64_a509b10e64184e5e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
           (EL2Enabled ())) <&&> (do
           (pure (! (← (ELUsingAArch32 EL2))))))) && (2 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (ELUsingAArch32 EL2)))) && (2 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
      else
        (do
          if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
          then writeReg AMEVCNTR0 (vectorUpdate (← readReg AMEVCNTR0) 2 (Mk_AMEVCNTR0_Type ((← (R_read t2)) +++ (← (R_read t)))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit)))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegWrite64_ffac5e218d5b074d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
           (EL2Enabled ())) <&&> (do
           (pure (! (← (ELUsingAArch32 EL2))))))) && (1 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (ELUsingAArch32 EL2)))) && (1 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
      else
        (do
          if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
          then writeReg AMEVCNTR0 (vectorUpdate (← readReg AMEVCNTR0) 1 (Mk_AMEVCNTR0_Type ((← (R_read t2)) +++ (← (R_read t)))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit)))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_06329c412b3ab5ff (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then (AMEVCNTR1_set 1 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_1415f513493b61c8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 10))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure (! (← (ELUsingAArch32 EL2))))))) && (10 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
      else
        (do
          if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                   (EL2Enabled ())) <&&> (do
                   (ELUsingAArch32 EL2)))) && (10 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
          else
            (do
              if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
              then (AMEVCNTR1_set 10 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_18488936f5130285 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 4))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then (AMEVCNTR1_set 4 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_3cf44094d12f6f9a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 12))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure (! (← (ELUsingAArch32 EL2))))))) && (12 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
      else
        (do
          if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                   (EL2Enabled ())) <&&> (do
                   (ELUsingAArch32 EL2)))) && (12 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
          else
            (do
              if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
              then (AMEVCNTR1_set 12 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_469c861805be726d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 15))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure (! (← (ELUsingAArch32 EL2))))))) && (15 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
      else
        (do
          if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                   (EL2Enabled ())) <&&> (do
                   (ELUsingAArch32 EL2)))) && (15 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
          else
            (do
              if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
              then (AMEVCNTR1_set 15 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_4a0c18bf00eccda4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then (AMEVCNTR1_set 2 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_683d5eccd985c418 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 8))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure (! (← (ELUsingAArch32 EL2))))))) && (8 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
      else
        (do
          if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                   (EL2Enabled ())) <&&> (do
                   (ELUsingAArch32 EL2)))) && (8 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
          else
            (do
              if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
              then (AMEVCNTR1_set 8 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_6aa1c0a95da044bc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 13))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure (! (← (ELUsingAArch32 EL2))))))) && (13 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
      else
        (do
          if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                   (EL2Enabled ())) <&&> (do
                   (ELUsingAArch32 EL2)))) && (13 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
          else
            (do
              if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
              then (AMEVCNTR1_set 13 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_80489a0c42f5990f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 3))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then (AMEVCNTR1_set 3 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_8a065d943b8f719e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 0))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then (AMEVCNTR1_set 0 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_8df7cb996ace4301 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 11))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure (! (← (ELUsingAArch32 EL2))))))) && (11 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
      else
        (do
          if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                   (EL2Enabled ())) <&&> (do
                   (ELUsingAArch32 EL2)))) && (11 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
          else
            (do
              if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
              then (AMEVCNTR1_set 11 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_8ea485840df13e8b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 6))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then (AMEVCNTR1_set 6 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_9589f0d5bbc35480 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 5))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then (AMEVCNTR1_set 5 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_a0a98205a8cc86f4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 7))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
      then (AMEVCNTR1_set 7 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_caa18a28b827223b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 14))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure (! (← (ELUsingAArch32 EL2))))))) && (14 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
      else
        (do
          if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                   (EL2Enabled ())) <&&> (do
                   (ELUsingAArch32 EL2)))) && (14 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
          else
            (do
              if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
              then (AMEVCNTR1_set 14 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_ec5133758c2bd694 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 9))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure (! (← (ELUsingAArch32 EL2))))))) && (9 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
      else
        (do
          if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                   (EL2Enabled ())) <&&> (do
                   (ELUsingAArch32 EL2)))) && (9 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
          else
            (do
              if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
              then (AMEVCNTR1_set 9 (Mk_AMEVCNTR1_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTHPS_CVAL_SysRegWrite64_34fa93164860ce59 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTKCTL_PL0PTEN ← (( do (pure (_get_CNTKCTL_Type_PL0PTEN (← (CNTKCTL_read__1 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PCEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_PL1PCEN ← (( do (pure (_get_CNTHCTL_Type_PL1PCEN (← (CNTHCTL_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__CNTKCTL_EL1_EL0PTEN == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__CNTKCTL_PL0PTEN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 0#1)) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PTEN == 0#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__CNTHCTL_PL1PCEN == 0#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                              then writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type ((← (R_read t2)) +++ (← (R_read t))))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                                  then writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type ((← (R_read t2)) +++ (← (R_read t))))
                                  else (CNTP_CVAL_write (Mk_CNTP_CVAL_Type ((← (R_read t2)) +++ (← (R_read t)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 0#1)) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__CNTHCTL_PL1PCEN == 0#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (ELUsingAArch32 EL3)))) : Bool)
                      then (CNTP_CVAL_NS_write (Mk_CNTP_CVAL_Type ((← (R_read t2)) +++ (← (R_read t)))))
                      else (CNTP_CVAL_write (Mk_CNTP_CVAL_Type ((← (R_read t2)) +++ (← (R_read t)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (CNTP_CVAL_NS_write (Mk_CNTP_CVAL_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (CNTP_CVAL_write (Mk_CNTP_CVAL_Type ((← (R_read t2)) +++ (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg CNTP_CVAL_S (Mk_CNTP_CVAL_Type ((← (R_read t2)) +++ (← (R_read t))))
                  else (CNTP_CVAL_NS_write (Mk_CNTP_CVAL_Type ((← (R_read t2)) +++ (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTHP_CVAL_SysRegWrite64_558ce8493f8ab75e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (CNTHP_CVAL_write (Mk_CNTHP_CVAL_Type ((← (R_read t2)) +++ (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (CNTHP_CVAL_write (Mk_CNTHP_CVAL_Type ((← (R_read t2)) +++ (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTHV_CVAL_SysRegWrite64_e72c3c45ec57bc51 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTKCTL_PL0VTEN ← (( do (pure (_get_CNTKCTL_Type_PL0VTEN (← (CNTKCTL_read__1 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__CNTKCTL_EL1_EL0VTEN == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__CNTKCTL_PL0VTEN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VTEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                           (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                      then writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type ((← (R_read t2)) +++ (← (R_read t))))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type ((← (R_read t2)) +++ (← (R_read t))))
                          else (CNTV_CVAL_write (Mk_CNTV_CVAL_Type ((← (R_read t2)) +++ (← (R_read t)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else (CNTV_CVAL_write (Mk_CNTV_CVAL_Type ((← (R_read t2)) +++ (← (R_read t))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (CNTV_CVAL_write (Mk_CNTV_CVAL_Type ((← (R_read t2)) +++ (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (CNTV_CVAL_write (Mk_CNTV_CVAL_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTVOFF_SysRegWrite64_772809c07f941c73 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (CNTVOFF_write ((← (R_read t2)) +++ (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (CNTVOFF_write ((← (R_read t2)) +++ (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def HTTBR_SysRegWrite64_3e34efab7aaa3ec6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T2 ← (( do (pure (_get_HSTR_EL2_Type_T2 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T2 ← (( do (pure (_get_HSTR_Type_T2 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T2 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T2 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg HTTBR (Mk_HTTBR_Type ((← (R_read t2)) +++ (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg HTTBR (Mk_HTTBR_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def ICC_ASGI1R_SysRegWrite64_29140bc551f7529b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TC ← (( do (pure (_get_ICH_HCR_EL2_Type_TC (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TC ← (( do (pure (_get_ICH_HCR_Type_TC (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FMO ← (( do (pure (_get_HCR_Type_FMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_IMO ← (( do (pure (_get_HCR_Type_IMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
               (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
               (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor))) <&&> (do
                   (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T12 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T12 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((__ICC_SRE_SRE == 0#1) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TC == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__ICH_HCR_TC == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FMO == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                          else
                                            (do
                                              if (((←((EL2Enabled ()) <&&> (do
                                                     (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                              else
                                                (do
                                                  if (((←((EL2Enabled ()) <&&> (do
                                                         (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                                  else
                                                    (do
                                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                                           (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                                                           (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                                                      then
                                                        (do
                                                          if ((←((Halted ()) <&&> (do
                                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                                      else
                                                        (do
                                                          if ((←((pure ((←((pure (HaveEL EL3)) <&&> (do (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor))) <&&> (do
                                                               (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
                                                          then
                                                            (do
                                                              if ((←((Halted ()) <&&> (do
                                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                              else (AArch32_TakeMonitorTrapException ()))
                                                          else (ICC_ASGI1R_write (Mk_ICC_ASGI1R_Type ((← (R_read t2)) +++ (← (R_read t))))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                   (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)) <&&> (do
                       (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                               (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              if ((←((pure (HaveEL EL3)) <&&> (do
                                   (ELUsingAArch32 EL3)) <&&> (do
                                   (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch32_TakeMonitorTrapException ()))
                              else (ICC_ASGI1R_write (Mk_ICC_ASGI1R_Type ((← (R_read t2)) +++ (← (R_read t))))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICC_ASGI1R_write (Mk_ICC_ASGI1R_Type ((← (R_read t2)) +++ (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def ICC_SGI0R_SysRegWrite64_3055f033253258da (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TC ← (( do (pure (_get_ICH_HCR_EL2_Type_TC (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TC ← (( do (pure (_get_ICH_HCR_Type_TC (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FMO ← (( do (pure (_get_HCR_Type_FMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_IMO ← (( do (pure (_get_HCR_Type_IMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
               (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
               (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor))) <&&> (do
                   (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T12 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T12 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((__ICC_SRE_SRE == 0#1) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TC == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__ICH_HCR_TC == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FMO == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                          else
                                            (do
                                              if (((←((EL2Enabled ()) <&&> (do
                                                     (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                              else
                                                (do
                                                  if (((←((EL2Enabled ()) <&&> (do
                                                         (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                                  else
                                                    (do
                                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                                           (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                                                           (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                                                      then
                                                        (do
                                                          if ((←((Halted ()) <&&> (do
                                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                                      else
                                                        (do
                                                          if ((←((pure ((←((pure (HaveEL EL3)) <&&> (do (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor))) <&&> (do
                                                               (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
                                                          then
                                                            (do
                                                              if ((←((Halted ()) <&&> (do
                                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                              else (AArch32_TakeMonitorTrapException ()))
                                                          else (ICC_SGI0R_write (Mk_ICC_SGI0R_Type ((← (R_read t2)) +++ (← (R_read t))))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                   (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)) <&&> (do
                       (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                               (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              if ((←((pure (HaveEL EL3)) <&&> (do
                                   (ELUsingAArch32 EL3)) <&&> (do
                                   (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch32_TakeMonitorTrapException ()))
                              else (ICC_SGI0R_write (Mk_ICC_SGI0R_Type ((← (R_read t2)) +++ (← (R_read t))))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICC_SGI0R_write (Mk_ICC_SGI0R_Type ((← (R_read t2)) +++ (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def ICC_SGI1R_SysRegWrite64_e5d73969c7266f22 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TC ← (( do (pure (_get_ICH_HCR_EL2_Type_TC (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TC ← (( do (pure (_get_ICH_HCR_Type_TC (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FMO ← (( do (pure (_get_HCR_Type_FMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_IMO ← (( do (pure (_get_HCR_Type_IMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
               (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
               (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((pure ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor))) <&&> (do
                   (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T12 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T12 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((__ICC_SRE_SRE == 0#1) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TC == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__ICH_HCR_TC == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FMO == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                          else
                                            (do
                                              if (((←((EL2Enabled ()) <&&> (do
                                                     (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                              else
                                                (do
                                                  if (((←((EL2Enabled ()) <&&> (do
                                                         (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                                  else
                                                    (do
                                                      if ((←((pure (HaveEL EL3)) <&&> (do
                                                           (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                                                           (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                                                      then
                                                        (do
                                                          if ((←((Halted ()) <&&> (do
                                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                                      else
                                                        (do
                                                          if ((←((pure ((←((pure (HaveEL EL3)) <&&> (do (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor))) <&&> (do
                                                               (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
                                                          then
                                                            (do
                                                              if ((←((Halted ()) <&&> (do
                                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                              else (AArch32_TakeMonitorTrapException ()))
                                                          else (ICC_SGI1R_write (Mk_ICC_SGI1R_Type ((← (R_read t2)) +++ (← (R_read t))))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                   (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)) <&&> (do
                       (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                               (pure (((_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) == 0b11#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              if ((←((pure (HaveEL EL3)) <&&> (do
                                   (ELUsingAArch32 EL3)) <&&> (do
                                   (pure (((_get_SCR_Type_IRQ (← readReg SCR)) +++ (_get_SCR_Type_FIQ (← readReg SCR))) == 0b11#2))))) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch32_TakeMonitorTrapException ()))
                              else (ICC_SGI1R_write (Mk_ICC_SGI1R_Type ((← (R_read t2)) +++ (← (R_read t))))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICC_SGI1R_write (Mk_ICC_SGI1R_Type ((← (R_read t2)) +++ (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def PAR_SysRegWrite64_867d7cbf8d644296 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
              else
                (do
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (ELUsingAArch32 EL3)))) : Bool)
                  then writeReg PAR_NS (Mk_PAR_Type ((← (R_read t2)) +++ (← (R_read t))))
                  else (PAR_write (Mk_PAR_Type ((← (R_read t2)) +++ (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then writeReg PAR_NS (Mk_PAR_Type ((← (R_read t2)) +++ (← (R_read t))))
              else (PAR_write (Mk_PAR_Type ((← (R_read t2)) +++ (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg PAR_S (Mk_PAR_Type ((← (R_read t2)) +++ (← (R_read t))))
                  else writeReg PAR_NS (Mk_PAR_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def PMCCNTR_SysRegWrite64_51a4ab1690d771a1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMCCNTR_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMCCNTR_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TPM ← (( do (pure (_get_HDCR_Type_TPM (← (HDCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
               (IsFeatureImplemented FEAT_PMUv3p9) <&&> (do
                 (pure (((_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) == 0b00#2))) <||> (do
                 (pure ((! (← (IsFeatureImplemented FEAT_PMUv3p9))) && (__PMUSERENR_EL0_EN == 0#1))))))) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMCCNTR_EL0 == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                      else (PMCCNTR_write (Mk_PMCCNTR_Type ((← (R_read t2)) +++ (← (R_read t))))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                              else (PMCCNTR_write (Mk_PMCCNTR_Type ((← (R_read t2)) +++ (← (R_read t)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                  else (PMCCNTR_write (Mk_PMCCNTR_Type ((← (R_read t2)) +++ (← (R_read t)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMCCNTR_write (Mk_PMCCNTR_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_SysRegWrite64_c1a707eccbf8dd96 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T2 ← (( do (pure (_get_HSTR_EL2_Type_T2 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T2 ← (( do (pure (_get_HSTR_Type_T2 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TVM ← (( do (pure (_get_HCR_Type_TVM (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T2 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T2 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then writeReg TTBR0_NS (Mk_TTBR0_Type ((← (R_read t2)) +++ (← (R_read t))))
                          else (TTBR0_write (Mk_TTBR0_Type ((← (R_read t2)) +++ (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then writeReg TTBR0_NS (Mk_TTBR0_Type ((← (R_read t2)) +++ (← (R_read t))))
              else (TTBR0_write (Mk_TTBR0_Type ((← (R_read t2)) +++ (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((←((pure (__SCR_NS == 0#1)) <&&> (do
                       (pure (BEq.beq (← readReg CP15SDISABLE) Signal_High))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then writeReg TTBR0_S (Mk_TTBR0_Type ((← (R_read t2)) +++ (← (R_read t))))
                      else writeReg TTBR0_NS (Mk_TTBR0_Type ((← (R_read t2)) +++ (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_SysRegWrite64_7d88e184b6073f76 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T2 ← (( do (pure (_get_HSTR_EL2_Type_T2 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T2 ← (( do (pure (_get_HSTR_Type_T2 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TVM ← (( do (pure (_get_HCR_Type_TVM (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T2 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T2 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then writeReg TTBR1_NS (Mk_TTBR1_Type ((← (R_read t2)) +++ (← (R_read t))))
                          else (TTBR1_write (Mk_TTBR1_Type ((← (R_read t2)) +++ (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then writeReg TTBR1_NS (Mk_TTBR1_Type ((← (R_read t2)) +++ (← (R_read t))))
              else (TTBR1_write (Mk_TTBR1_Type ((← (R_read t2)) +++ (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((←((pure (__SCR_NS == 0#1)) <&&> (do
                       (pure (BEq.beq (← readReg CP15SDISABLE2) Signal_High))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then writeReg TTBR1_S (Mk_TTBR1_Type ((← (R_read t2)) +++ (← (R_read t))))
                      else writeReg TTBR1_NS (Mk_TTBR1_Type ((← (R_read t2)) +++ (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def VTTBR_SysRegWrite64_ab86e13c6c48344f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T2 ← (( do (pure (_get_HSTR_EL2_Type_T2 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T2 ← (( do (pure (_get_HSTR_Type_T2 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T2 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T2 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg VTTBR (Mk_VTTBR_Type ((← (R_read t2)) +++ (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg VTTBR (Mk_VTTBR_Type ((← (R_read t2)) +++ (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ACTLR2_SysRegRead32_b5235ae9298d37ab (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TACR ← (( do (pure (_get_HCR_EL2_Type_TACR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TAC ← (( do (pure (_get_HCR_Type_TAC (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T1 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T1 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TACR == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TAC == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (R_set t (← (ACTLR2_NS_read ())))
                          else (R_set t (← (ACTLR2_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (ACTLR2_NS_read ())))
              else (R_set t (← (ACTLR2_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg ACTLR2_S))
                  else (R_set t (← (ACTLR2_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ACTLR_SysRegRead32_6cec3685fb7200c1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TACR ← (( do (pure (_get_HCR_EL2_Type_TACR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TAC ← (( do (pure (_get_HCR_Type_TAC (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T1 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T1 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TACR == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TAC == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (R_set t (← (ACTLR_NS_read ())))
                          else (R_set t (← (ACTLR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (ACTLR_NS_read ())))
              else (R_set t (← (ACTLR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg ACTLR_S))
                  else (R_set t (← (ACTLR_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ADFSR_SysRegRead32_12834f15645083f8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TRVM ← (( do (pure (_get_HCR_Type_TRVM (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T5 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T5 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TRVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TRVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (R_set t (← (ADFSR_NS_read ())))
                          else (R_set t (← (ADFSR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (ADFSR_NS_read ())))
              else (R_set t (← (ADFSR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg ADFSR_S))
                  else (R_set t (← (ADFSR_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AIDR_SysRegRead32_ce556bd47a2bd19b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID1 ← (( do (pure (_get_HCR_EL2_Type_TID1 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TID1 ← (( do (pure (_get_HCR_Type_TID1 (← (HCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T0 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T0 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TID1 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TID1 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else (R_set t (← (AIDR_read ())))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (AIDR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (AIDR_read ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AIFSR_SysRegRead32_dcd7a0d08b788988 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TRVM ← (( do (pure (_get_HCR_Type_TRVM (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T5 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T5 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TRVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TRVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (R_set t (← (AIFSR_NS_read ())))
                          else (R_set t (← (AIFSR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (AIFSR_NS_read ())))
              else (R_set t (← (AIFSR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg AIFSR_S))
                  else (R_set t (← (AIFSR_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR0_SysRegRead32_9c3a882cb83d441e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T10 ← (( do (pure (_get_HSTR_EL2_Type_T10 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T10 ← (( do (pure (_get_HSTR_Type_T10 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TRVM ← (( do (pure (_get_HCR_Type_TRVM (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T10 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T10 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TRVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TRVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (R_set t (← (AMAIR0_NS_read ())))
                          else (R_set t (← (AMAIR0_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (AMAIR0_NS_read ())))
              else (R_set t (← (AMAIR0_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg AMAIR0_S))
                  else (R_set t (← (AMAIR0_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR1_SysRegRead32_abbf588378c53393 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T10 ← (( do (pure (_get_HSTR_EL2_Type_T10 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T10 ← (( do (pure (_get_HSTR_Type_T10 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TRVM ← (( do (pure (_get_HCR_Type_TRVM (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T10 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T10 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TRVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TRVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (R_set t (← (AMAIR1_NS_read ())))
                          else (R_set t (← (AMAIR1_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (AMAIR1_NS_read ())))
              else (R_set t (← (AMAIR1_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg AMAIR1_S))
                  else (R_set t (← (AMAIR1_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCFGR_SysRegRead32_f4b1155615a324f5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMCFGR (← (AMCFGR_read ()))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMCFGR (← (AMCFGR_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMCFGR (← (AMCFGR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMCFGR (← (AMCFGR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCGCR_SysRegRead32_ec0083efd88e8df5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMCGCR (← (AMCGCR_read ()))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMCGCR (← (AMCGCR_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMCGCR (← (AMCGCR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMCGCR (← (AMCGCR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCNTENCLR0_SysRegRead32_4cd517564ca44d4e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMCNTEN0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMCNTEN0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if ((((←((EL2Enabled ()) <&&> (do
                                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN0 == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                      else (R_set t (__get_AMCNTENCLR0 (← (AMCNTENCLR0_read ())))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMCNTENCLR0 (← (AMCNTENCLR0_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMCNTENCLR0 (← (AMCNTENCLR0_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMCNTENCLR0 (← (AMCNTENCLR0_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCNTENCLR1_SysRegRead32_d9e05aee283dea2c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMCNTEN1 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMCNTEN1 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if ((((←((EL2Enabled ()) <&&> (do
                                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN1 == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                      else (R_set t (__get_AMCNTENCLR1 (← (AMCNTENCLR1_read ())))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMCNTENCLR1 (← (AMCNTENCLR1_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMCNTENCLR1 (← (AMCNTENCLR1_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMCNTENCLR1 (← (AMCNTENCLR1_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCNTENSET0_SysRegRead32_941308a2fea42e28 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMCNTEN0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMCNTEN0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if ((((←((EL2Enabled ()) <&&> (do
                                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN0 == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                      else (R_set t (__get_AMCNTENSET0 (← (AMCNTENSET0_read ())))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMCNTENSET0 (← (AMCNTENSET0_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMCNTENSET0 (← (AMCNTENSET0_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMCNTENSET0 (← (AMCNTENSET0_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCNTENSET1_SysRegRead32_7b7457f3c7ff281b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMCNTEN1 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMCNTEN1 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if ((((←((EL2Enabled ()) <&&> (do
                                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMCNTEN1 == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                      else (R_set t (__get_AMCNTENSET1 (← (AMCNTENSET1_read ())))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMCNTENSET1 (← (AMCNTENSET1_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMCNTENSET1 (← (AMCNTENSET1_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMCNTENSET1 (← (AMCNTENSET1_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCR_SysRegRead32_3740e4968cc5855a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMCR (← (AMCR_read ()))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMCR (← (AMCR_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMCR (← (AMCR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMCR (← (AMCR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER0_SysRegRead32_2bb2f6721c44cef6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 1))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 1))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER0_SysRegRead32_2e79e456f9d1dcd3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 2))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 2))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 2))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER0_SysRegRead32_3d4ae79d0a2a83f7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 0))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 0))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 0))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER0_SysRegRead32_d72cb28d75eca03e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 3))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 3))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 3))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMEVTYPER0 (← (AMEVTYPER0_read 3))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_30353b694529c623 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER114_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER114_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 14))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER114_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 14)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 14))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 14))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 14))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_3704564c9ad105a9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER115_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER115_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 15))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER115_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 15)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 15))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 15))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 15))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_3d5ee14ab14e0600 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER111_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER111_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 11))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER111_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 11)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 11))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 11))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 11))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_3f1d2f749c9eacac (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER12_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER12_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER12_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 2)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 2))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 2))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 2))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_56620f65cf2520b9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER110_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER110_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 10))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER110_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 10)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 10))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 10))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 10))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_5da5d2022384b9e4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER13_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER13_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 3))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER13_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 3)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 3))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 3))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 3))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_6862bf1fd0c624fa (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER11_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER11_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER11_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 1)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 1))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 1))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 1))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_727db649d7fd62f8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER112_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER112_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 12))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER112_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 12)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 12))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 12))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 12))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_72835fc6dfc4b11f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER18_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER18_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 8))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER18_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 8)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 8))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 8))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 8))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_a5bece13ef847a3b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER10_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER10_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 0))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER10_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 0)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 0))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 0))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 0))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_aefd3ad06352acdf (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER15_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER15_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 5))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER15_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 5)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 5))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 5))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 5))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_b4ee1ae1a6a9e5fe (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER113_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER113_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 13))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER113_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 13)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 13))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 13))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 13))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_bc839289c9bacd64 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER14_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER14_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 4))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER14_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 4)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 4))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 4))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 4))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_d76669b6678fb9d9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER16_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER16_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 6))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER16_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 6)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 6))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 6))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 6))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_e5dbca925a693d3a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER17_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER17_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 7))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER17_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 7)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 7))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 7))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 7))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_ecafc26f65f1dda2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVTYPER19_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVTYPER19_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 9))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__AMUSERENR_EL0_EN == 0#1)) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
                  then
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVTYPER19_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                          else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 9)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 9))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 9))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_AMEVTYPER1 (← (AMEVTYPER1_read 9))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AMUSERENR_SysRegRead32_a8f18bf4f7170234 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (R_set t (__get_AMUSERENR (← (AMUSERENR_read ()))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (__get_AMUSERENR (← (AMUSERENR_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_AMUSERENR (← (AMUSERENR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_AMUSERENR (← (AMUSERENR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CCSIDR2_SysRegRead32_b747ebd0fcc6df4e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID4 ← (( do (pure (_get_HCR_EL2_Type_TID4 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TID2 ← (( do (pure (_get_HCR_Type_TID2 (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TID4 ← (( do (pure (_get_HCR2_Type_TID4 (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T0 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T0 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TID2 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TID4 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TID2 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TID4 == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (R_set t (__get_CCSIDR2 (← (CCSIDR2_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (__get_CCSIDR2 (← (CCSIDR2_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_CCSIDR2 (← (CCSIDR2_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CCSIDR_SysRegRead32_4e417948cc9050d5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID4 ← (( do (pure (_get_HCR_EL2_Type_TID4 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TID2 ← (( do (pure (_get_HCR_Type_TID2 (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TID4 ← (( do (pure (_get_HCR2_Type_TID4 (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T0 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T0 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TID2 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TID4 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TID2 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TID4 == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (R_set t (← (CCSIDR_read ())))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (CCSIDR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (CCSIDR_read ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CLIDR_SysRegRead32_1324f310591d527a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID4 ← (( do (pure (_get_HCR_EL2_Type_TID4 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TID2 ← (( do (pure (_get_HCR_Type_TID2 (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TID4 ← (( do (pure (_get_HCR2_Type_TID4 (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T0 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T0 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TID2 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TID4 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TID2 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TID4 == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (R_set t (← (CLIDR_read ())))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (CLIDR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (CLIDR_read ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTFRQ_SysRegRead32_4d7a0faa14f3d1f9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTKCTL_PL0PCTEN ← (( do (pure (_get_CNTKCTL_Type_PL0PCTEN (← (CNTKCTL_read__1 ())))) ) : SailM (BitVec 1) )
  let __CNTKCTL_PL0VCTEN ← (( do (pure (_get_CNTKCTL_Type_PL0VCTEN (← (CNTKCTL_read__1 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
           (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))) <&&> (do
           (pure (((_get_CNTKCTL_EL1_Type_EL0PCTEN (← readReg CNTKCTL_EL1)) +++ (_get_CNTKCTL_EL1_Type_EL0VCTEN (← readReg CNTKCTL_EL1))) == 0b00#2))))) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
      else
        (do
          if ((((← (ELUsingAArch32 EL1)) && (__CNTKCTL_PL0PCTEN == 0#1)) && (__CNTKCTL_PL0VCTEN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                   (pure (((_get_CNTHCTL_EL2_Type_EL0PCTEN (← readReg CNTHCTL_EL2)) +++ (_get_CNTHCTL_EL2_Type_EL0VCTEN (← readReg CNTHCTL_EL2))) == 0b00#2))))) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (R_set t (← (CNTFRQ_read ()))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (R_set t (← (CNTFRQ_read ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (CNTFRQ_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (CNTFRQ_read ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHCTL_SysRegRead32_36df328680cb805f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (__get_CNTHCTL (← (CNTHCTL_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_CNTHCTL (← (CNTHCTL_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHPS_CTL_SysRegRead32_a99d410e49082e9f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTKCTL_PL0PTEN ← (( do (pure (_get_CNTKCTL_Type_PL0PTEN (← (CNTKCTL_read__1 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PCEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_PL1PCEN ← (( do (pure (_get_CNTHCTL_Type_PL1PCEN (← (CNTHCTL_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__CNTKCTL_EL1_EL0PTEN == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__CNTKCTL_PL0PTEN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 0#1)) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PTEN == 0#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__CNTHCTL_PL1PCEN == 0#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                              then (R_set t (Sail.BitVec.extractLsb (__get_CNTHPS_CTL_EL2 (← readReg CNTHPS_CTL_EL2)) 31 0))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                                  then (R_set t (Sail.BitVec.extractLsb (__get_CNTHP_CTL_EL2 (← readReg CNTHP_CTL_EL2)) 31 0))
                                  else (R_set t (__get_CNTP_CTL (← (CNTP_CTL_read ()))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 0#1)) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__CNTHCTL_PL1PCEN == 0#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (ELUsingAArch32 EL3)))) : Bool)
                      then (R_set t (__get_CNTP_CTL_NS (← (CNTP_CTL_NS_read ()))))
                      else (R_set t (__get_CNTP_CTL (← (CNTP_CTL_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (__get_CNTP_CTL_NS (← (CNTP_CTL_NS_read ()))))
              else (R_set t (__get_CNTP_CTL (← (CNTP_CTL_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (__get_CNTP_CTL_S (← readReg CNTP_CTL_S)))
                  else (R_set t (__get_CNTP_CTL_NS (← (CNTP_CTL_NS_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_CTL_SysRegRead32_5ea09b260a579171 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (__get_CNTHP_CTL (← (CNTHP_CTL_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_CNTHP_CTL (← (CNTHP_CTL_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_SysRegRead32_ea212b21a99af571 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTHP_CTL_ENABLE ← (( do (pure (_get_CNTHP_CTL_Type_ENABLE (← (CNTHP_CTL_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
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
              if ((__CNTHP_CTL_ENABLE == 0#1) : Bool)
              then (R_set t (← (__UNKNOWN_bits 32)))
              else (R_set t (Sail.BitVec.extractLsb ((← (CNTHP_CVAL_read ())) - (← (PhysicalCountInt ()))) 31 0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__CNTHP_CTL_ENABLE == 0#1) : Bool)
                      then (R_set t (← (__UNKNOWN_bits 32)))
                      else (R_set t (Sail.BitVec.extractLsb ((← (CNTHP_CVAL_read ())) - (← (PhysicalCountInt ()))) 31 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_SysRegRead32_fdd1a67f3e306983 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTKCTL_PL0PTEN ← (( do (pure (_get_CNTKCTL_Type_PL0PTEN (← (CNTKCTL_read__1 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PCEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_PL1PCEN ← (( do (pure (_get_CNTHCTL_Type_PL1PCEN (← (CNTHCTL_read ())))) ) : SailM (BitVec 1) )
  let __CNTHPS_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHPS_CTL_EL2_Type_ENABLE (← readReg CNTHPS_CTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHP_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHP_CTL_EL2_Type_ENABLE (← readReg CNTHP_CTL_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ECVEn ← (( do (pure (_get_SCR_EL3_Type_ECVEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_ECV ← (( do (pure (_get_CNTHCTL_EL2_Type_ECV (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTP_CTL_ENABLE ← (( do (pure (_get_CNTP_CTL_Type_ENABLE (← (CNTP_CTL_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  let __CNTP_CTL_NS_ENABLE ← (( do (pure (_get_CNTP_CTL_Type_ENABLE (← (CNTP_CTL_NS_read ())))) ) : SailM (BitVec 1) )
  let __CNTP_CTL_S_ENABLE ← (( do (pure (_get_CNTP_CTL_Type_ENABLE (← readReg CNTP_CTL_S))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__CNTKCTL_EL1_EL0PTEN == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__CNTKCTL_PL0PTEN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 0#1)) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PTEN == 0#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__CNTHCTL_PL1PCEN == 0#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                              then
                                (do
                                  if ((__CNTHPS_CTL_EL2_ENABLE == 0#1) : Bool)
                                  then (R_set t (← (__UNKNOWN_bits 32)))
                                  else (R_set t (Sail.BitVec.extractLsb ((← readReg CNTHPS_CVAL_EL2) - (← (PhysicalCountInt ()))) 31 0)))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                                  then
                                    (do
                                      if ((__CNTHP_CTL_EL2_ENABLE == 0#1) : Bool)
                                      then (R_set t (← (__UNKNOWN_bits 32)))
                                      else (R_set t (Sail.BitVec.extractLsb ((← readReg CNTHP_CVAL_EL2) - (← (PhysicalCountInt ()))) 31 0)))
                                  else
                                    (do
                                      if ((←((pure (((←((IsFeatureImplemented FEAT_ECV) <&&> (do (EL2Enabled ())) <&&> (do (pure (! (← (ELUsingAArch32 EL2))))))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1))) <&&> (do
                                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) : Bool)
                                      then
                                        (do
                                          if ((__CNTP_CTL_ENABLE == 0#1) : Bool)
                                          then (R_set t (← (__UNKNOWN_bits 32)))
                                          else (R_set t (Sail.BitVec.extractLsb ((← (CNTP_CVAL_read ())) - ((← (PhysicalCountInt ())) - (← readReg CNTPOFF_EL2))) 31 0)))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) : Bool)
                                          then
                                            (do
                                              if ((__SCR_NS == 1#1) : Bool)
                                              then
                                                (do
                                                  if ((__CNTP_CTL_NS_ENABLE == 0#1) : Bool)
                                                  then (R_set t (← (__UNKNOWN_bits 32)))
                                                  else (R_set t (Sail.BitVec.extractLsb ((← (CNTP_CVAL_NS_read ())) - (← (PhysicalCountInt ()))) 31 0)))
                                              else
                                                (do
                                                  if ((__CNTP_CTL_S_ENABLE == 0#1) : Bool)
                                                  then (R_set t (← (__UNKNOWN_bits 32)))
                                                  else (R_set t (Sail.BitVec.extractLsb ((← readReg CNTP_CVAL_S) - (← (PhysicalCountInt ()))) 31 0))))
                                          else
                                            (do
                                              if ((__CNTP_CTL_ENABLE == 0#1) : Bool)
                                              then (R_set t (← (__UNKNOWN_bits 32)))
                                              else (R_set t (Sail.BitVec.extractLsb ((← (CNTP_CVAL_read ())) - (← (PhysicalCountInt ()))) 31 0)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 0#1)) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__CNTHCTL_PL1PCEN == 0#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((((←((IsFeatureImplemented FEAT_ECV) <&&> (do
                               (EL2Enabled ())) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL2))))))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1)) : Bool)
                      then
                        (do
                          if ((__CNTP_CTL_ENABLE == 0#1) : Bool)
                          then (R_set t (← (__UNKNOWN_bits 32)))
                          else (R_set t (Sail.BitVec.extractLsb ((← (CNTP_CVAL_read ())) - ((← (PhysicalCountInt ())) - (← readReg CNTPOFF_EL2))) 31 0)))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then
                            (do
                              if ((__CNTP_CTL_NS_ENABLE == 0#1) : Bool)
                              then (R_set t (← (__UNKNOWN_bits 32)))
                              else (R_set t (Sail.BitVec.extractLsb ((← (CNTP_CVAL_NS_read ())) - (← (PhysicalCountInt ()))) 31 0)))
                          else
                            (do
                              if ((__CNTP_CTL_ENABLE == 0#1) : Bool)
                              then (R_set t (← (__UNKNOWN_bits 32)))
                              else (R_set t (Sail.BitVec.extractLsb ((← (CNTP_CVAL_read ())) - (← (PhysicalCountInt ()))) 31 0))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then
                (do
                  if ((__CNTP_CTL_NS_ENABLE == 0#1) : Bool)
                  then (R_set t (← (__UNKNOWN_bits 32)))
                  else (R_set t (Sail.BitVec.extractLsb ((← (CNTP_CVAL_NS_read ())) - (← (PhysicalCountInt ()))) 31 0)))
              else
                (do
                  if ((__CNTP_CTL_ENABLE == 0#1) : Bool)
                  then (R_set t (← (__UNKNOWN_bits 32)))
                  else (R_set t (Sail.BitVec.extractLsb ((← (CNTP_CVAL_read ())) - (← (PhysicalCountInt ()))) 31 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      if ((__CNTP_CTL_S_ENABLE == 0#1) : Bool)
                      then (R_set t (← (__UNKNOWN_bits 32)))
                      else (R_set t (Sail.BitVec.extractLsb ((← readReg CNTP_CVAL_S) - (← (PhysicalCountInt ()))) 31 0)))
                  else
                    (do
                      if ((__CNTP_CTL_NS_ENABLE == 0#1) : Bool)
                      then (R_set t (← (__UNKNOWN_bits 32)))
                      else (R_set t (Sail.BitVec.extractLsb ((← (CNTP_CVAL_NS_read ())) - (← (PhysicalCountInt ()))) 31 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHVS_CTL_SysRegRead32_a44e5d4ed8fbfe64 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTKCTL_PL0VTEN ← (( do (pure (_get_CNTKCTL_Type_PL0VTEN (← (CNTKCTL_read__1 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__CNTKCTL_EL1_EL0VTEN == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__CNTKCTL_PL0VTEN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VTEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                           (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                      then (R_set t (Sail.BitVec.extractLsb (__get_CNTHVS_CTL_EL2 (← readReg CNTHVS_CTL_EL2)) 31 0))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then (R_set t (Sail.BitVec.extractLsb (__get_CNTHV_CTL_EL2 (← readReg CNTHV_CTL_EL2)) 31 0))
                          else (R_set t (__get_CNTV_CTL (← (CNTV_CTL_read ()))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else (R_set t (__get_CNTV_CTL (← (CNTV_CTL_read ())))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (__get_CNTV_CTL (← (CNTV_CTL_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_CNTV_CTL (← (CNTV_CTL_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTKCTL_SysRegRead32_9166ed3878001f60 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (R_set t (__get_CNTKCTL (← (CNTKCTL_read__1 ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (__get_CNTKCTL (← (CNTKCTL_read__1 ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_CNTKCTL (← (CNTKCTL_read__1 ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTV_TVAL_SysRegRead32_ac1a47c2d11f8dd9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTKCTL_PL0VTEN ← (( do (pure (_get_CNTKCTL_Type_PL0VTEN (← (CNTKCTL_read__1 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHVS_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHVS_CTL_EL2_Type_ENABLE (← readReg CNTHVS_CTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHV_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHV_CTL_EL2_Type_ENABLE (← readReg CNTHV_CTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTV_CTL_ENABLE ← (( do (pure (_get_CNTV_CTL_Type_ENABLE (← (CNTV_CTL_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__CNTKCTL_EL1_EL0VTEN == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__CNTKCTL_PL0VTEN == 0#1)) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HCR_TGE == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VTEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                           (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                      then
                        (do
                          if ((__CNTHVS_CTL_EL2_ENABLE == 0#1) : Bool)
                          then (R_set t (← (__UNKNOWN_bits 32)))
                          else (R_set t (Sail.BitVec.extractLsb ((← readReg CNTHVS_CVAL_EL2) - (← (PhysicalCountInt ()))) 31 0)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then
                            (do
                              if ((__CNTHV_CTL_EL2_ENABLE == 0#1) : Bool)
                              then (R_set t (← (__UNKNOWN_bits 32)))
                              else (R_set t (Sail.BitVec.extractLsb ((← readReg CNTHV_CVAL_EL2) - (← (PhysicalCountInt ()))) 31 0)))
                          else
                            (do
                              if ((__CNTV_CTL_ENABLE == 0#1) : Bool)
                              then (R_set t (← (__UNKNOWN_bits 32)))
                              else
                                (do
                                  if ((←((pure (HaveEL EL2)) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
                                  then (R_set t (Sail.BitVec.extractLsb ((← (CNTV_CVAL_read ())) - ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2))) 31 0))
                                  else
                                    (do
                                      if ((←((pure (HaveEL EL2)) <&&> (do
                                           (ELUsingAArch32 EL2)))) : Bool)
                                      then (R_set t (Sail.BitVec.extractLsb ((← (CNTV_CVAL_read ())) - ((← (PhysicalCountInt ())) - (← (CNTVOFF_read ())))) 31 0))
                                      else (R_set t (Sail.BitVec.extractLsb ((← (CNTV_CVAL_read ())) - (← (PhysicalCountInt ()))) 31 0)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if ((__CNTV_CTL_ENABLE == 0#1) : Bool)
              then (R_set t (← (__UNKNOWN_bits 32)))
              else
                (do
                  if ((←((pure (HaveEL EL2)) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
                  then (R_set t (Sail.BitVec.extractLsb ((← (CNTV_CVAL_read ())) - ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2))) 31 0))
                  else
                    (do
                      if ((←((pure (HaveEL EL2)) <&&> (do
                           (ELUsingAArch32 EL2)))) : Bool)
                      then (R_set t (Sail.BitVec.extractLsb ((← (CNTV_CVAL_read ())) - ((← (PhysicalCountInt ())) - (← (CNTVOFF_read ())))) 31 0))
                      else (R_set t (Sail.BitVec.extractLsb ((← (CNTV_CVAL_read ())) - (← (PhysicalCountInt ()))) 31 0))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__CNTV_CTL_ENABLE == 0#1) : Bool)
              then (R_set t (← (__UNKNOWN_bits 32)))
              else (R_set t (Sail.BitVec.extractLsb ((← (CNTV_CVAL_read ())) - ((← (PhysicalCountInt ())) - (← (CNTVOFF_read ())))) 31 0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTV_CTL_ENABLE == 0#1) : Bool)
                  then (R_set t (← (__UNKNOWN_bits 32)))
                  else
                    (do
                      if ((HaveEL EL2) : Bool)
                      then (R_set t (Sail.BitVec.extractLsb ((← (CNTV_CVAL_read ())) - ((← (PhysicalCountInt ())) - (← (CNTVOFF_read ())))) 31 0))
                      else (R_set t (Sail.BitVec.extractLsb ((← (CNTV_CVAL_read ())) - (← (PhysicalCountInt ()))) 31 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CONTEXTIDR_SysRegRead32_a8d33c511e223d46 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TRVM ← (( do (pure (_get_HCR_Type_TRVM (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TRVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TRVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (R_set t (← (CONTEXTIDR_NS_read ())))
                          else (R_set t (← (CONTEXTIDR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (CONTEXTIDR_NS_read ())))
              else (R_set t (← (CONTEXTIDR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg CONTEXTIDR_S))
                  else (R_set t (← (CONTEXTIDR_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPACR_SysRegRead32_3e95a711394f5115 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TCPAC ← (( do (pure (_get_CPTR_EL3_Type_TCPAC (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TCPAC ← (( do (pure (_get_CPTR_EL2_Type_TCPAC (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TCPAC ← (( do (pure (_get_HCPTR_Type_TCPAC (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T1 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T1 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TCPAC == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TCPAC == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (R_set t (← (__get_CPACR (← (CPACR_read__1 ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (← (__get_CPACR (← (CPACR_read__1 ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (__get_CPACR (← (CPACR_read__1 ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CSSELR_SysRegRead32_b9908a214e4391b4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID4 ← (( do (pure (_get_HCR_EL2_Type_TID4 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TID2 ← (( do (pure (_get_HCR_Type_TID2 (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TID4 ← (( do (pure (_get_HCR2_Type_TID4 (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T0 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T0 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TID2 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TID4 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TID2 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TID4 == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if ((←((pure (HaveEL EL3)) <&&> (do
                                       (ELUsingAArch32 EL3)))) : Bool)
                                  then (R_set t (__get_CSSELR_NS (← (CSSELR_NS_read ()))))
                                  else (R_set t (__get_CSSELR (← (CSSELR_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (__get_CSSELR_NS (← (CSSELR_NS_read ()))))
              else (R_set t (__get_CSSELR (← (CSSELR_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (__get_CSSELR_S (← readReg CSSELR_S)))
                  else (R_set t (__get_CSSELR_NS (← (CSSELR_NS_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CTR_SysRegRead32_99a8e042837c333b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TID2 ← (( do (pure (_get_HCR_Type_TID2 (← (HCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T0 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T0 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TID2 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TID2 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else (R_set t (__get_CTR (← (CTR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (__get_CTR (← (CTR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_CTR (← (CTR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DACR_SysRegRead32_a5e223b70013760e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T3 ← (( do (pure (_get_HSTR_EL2_Type_T3 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T3 ← (( do (pure (_get_HSTR_Type_T3 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TRVM ← (( do (pure (_get_HCR_Type_TRVM (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T3 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T3 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TRVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TRVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (R_set t (← (DACR_NS_read ())))
                          else (R_set t (← (DACR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (DACR_NS_read ())))
              else (R_set t (← (DACR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg DACR_S))
                  else (R_set t (← (DACR_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGAUTHSTATUS_SysRegRead32_e99aa927d23f6bfc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                   (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (ELUsingAArch32 EL2)) <&&> (do
                       (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else (R_set t (__get_DBGAUTHSTATUS (← (DBGAUTHSTATUS_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                  else (R_set t (__get_DBGAUTHSTATUS (← (DBGAUTHSTATUS_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DBGAUTHSTATUS (← (DBGAUTHSTATUS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_01c2798f5fc44bfa (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((6 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 6)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 6)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 6)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_0c66b90b6558a3cb (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((1 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 1)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 1)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 1)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_216d13962e754b99 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((12 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 12)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 12)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 12)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_2a19913e0ff50654 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((9 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 9)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 9)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 9)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_2c7e30fbae6d4b48 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((0 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 0)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 0)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_4aa006511c22539c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((2 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 2)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 2)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 2)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_4c18d60e0902660d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((3 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 3)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 3)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 3)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_524a8653177fde8f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((5 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 5)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 5)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 5)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_5711831aec3ae94d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((14 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 14)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 14)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 14)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_8fb0687c13a9ae99 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((13 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 13)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 13)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 13)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_afe89ec5412ea81e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((10 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 10)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 10)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 10)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_cbd47314947043c8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((15 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 15)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 15)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 15)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_cdd1fd850dc45db5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((8 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 8)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 8)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 8)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_db1b198c49f933c0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((4 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 4)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 4)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 4)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_e0d675a59f2b5c3e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((7 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 7)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 7)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 7)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegRead32_f6f0a6ec5a19d902 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((11 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (__get_DBGBCR (← (DBGBCR_read 11)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (__get_DBGBCR (← (DBGBCR_read 11)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGBCR (← (DBGBCR_read 11)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_00f589dd9b6e498d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((4 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 4))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 4))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 4))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_08fe9e5e419581ae (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((8 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 8))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 8))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 8))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_0d7192e87273fee3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((7 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 7))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 7))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 7))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_1730a99ffdcdb940 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((2 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 2))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 2))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 2))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_3127ee8e7174eb76 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((13 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 13))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 13))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 13))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_3b08f67b830efeb5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((12 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 12))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 12))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 12))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_4a2928b59ff2bd88 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((10 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 10))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 10))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 10))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_4b2492f939b2d68d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((3 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 3))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 3))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 3))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_54fa7eb1a8a086d2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((1 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 1))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 1))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 1))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_731a4ca5463f9ac4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((15 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 15))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 15))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 15))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_7547e126cd447504 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((6 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 6))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 6))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 6))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_7ba934859e2de1ac (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((14 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 14))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 14))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 14))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_82067dc9734a6b24 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((5 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 5))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 5))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 5))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_aeb056e353dc1a63 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((9 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 9))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 9))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 9))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_c036021238cbadaa (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((0 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 0))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 0))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 0))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_SysRegRead32_c4752bdaff15ec68 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((11 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBVR_read 11))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBVR_read 11))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBVR_read 11))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_1c27a604d2b4f32b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((14 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 14))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 14))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 14))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_4c6fa7f444c624cb (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((4 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 4))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 4))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 4))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_52c85c2c5daef517 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((5 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 5))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 5))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 5))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_56d437c5026e56e6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((9 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 9))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 9))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 9))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_718e496a0f71d413 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((0 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 0))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 0))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 0))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_745a1f5c08c2c352 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((11 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 11))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 11))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 11))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_7511d8f154b2cfe2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((15 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 15))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 15))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 15))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_78ef58571ab2de22 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((6 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 6))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 6))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 6))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_7ae84360e0b64934 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((8 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 8))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 8))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 8))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_8e4aad430b2ecf98 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((7 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 7))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 7))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 7))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_9a88c64f6ef204ae (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((2 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 2))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 2))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 2))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_dac7cb34b3ce5d73 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((1 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 1))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 1))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 1))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_e8fd3bc58d8acce2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((10 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 10))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 10))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 10))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_e9303c37358e3794 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((13 ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
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
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (R_set t (← (DBGBXVR_read 13))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (R_set t (← (DBGBXVR_read 13))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 13))))
                  else (pure ())))))


