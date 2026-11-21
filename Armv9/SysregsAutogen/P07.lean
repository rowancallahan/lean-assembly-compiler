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
def RMR_EL2_SysRegWrite_fb0b01388c042301 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
           (EL2Enabled ())))) && (IsHighestEL EL2)) && (__HCR_EL2_NV == 1#1)) : Bool)
  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
  else
    (do
      if ((((← readReg PSTATE).EL == EL2) && (IsHighestEL EL2)) : Bool)
      then writeReg RMR_EL2 (Mk_RMR_EL2_Type (← (X_read t 64)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))

/-- Type quantifiers: t : Int -/
def RMR_EL3_SysRegWrite_d2303115883d7964 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((((← readReg PSTATE).EL == EL3) && (IsHighestEL EL3)) : Bool)
  then writeReg RMR_EL3 (Mk_RMR_EL3_Type (← (X_read t 64)))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def S2PIR_EL2_SysRegWrite_137a77ca21811a8a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x2B0#12) (← (X_read t 64)))
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
                  else writeReg S2PIR_EL2 (Mk_S2PIR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg S2PIR_EL2 (Mk_S2PIR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def S2POR_EL1_SysRegWrite_9557ee7f2cc1821f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_PIEn ← (( do (pure (_get_SCR_EL3_Type_PIEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nS2POR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_nS2POR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((← (EL2Enabled ())) && (__HCR_EL2_TVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nS2POR_EL1 == 0#1)) : Bool)
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
                          then (NVMem_set (BitVec.toNat 0x2B8#12) (← (X_read t 64)))
                          else writeReg S2POR_EL1 (Mk_S2POR_EL1_Type (← (X_read t 64))))))))
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
                  else writeReg S2POR_EL1 (Mk_S2POR_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg S2POR_EL1 (Mk_S2POR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AArch64_ImpDefSysRegWrite (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (t : Int) : SailM Unit := do
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def SCR_EL3_SysRegWrite_b664c319973b52d6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg SCR_EL3 (Mk_SCR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR2_EL1_SysRegWrite_42dbeb1a93efc9fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x278#12) (← (X_read t 64)))
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
                      else writeReg SCTLR2_EL1 (Mk_SCTLR2_EL1_Type (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg SCTLR2_EL1 (Mk_SCTLR2_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR2_EL1_SysRegWrite_83a6f9f68c57ef4e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_SCTLR2En ← (( do (pure (_get_SCR_EL3_Type_SCTLR2En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_SCTLR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_SCTLR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((← (EL2Enabled ())) && (__HCR_EL2_TVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_SCTLR_EL1 == 1#1)) : Bool)
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
                              then (NVMem_set (BitVec.toNat 0x278#12) (← (X_read t 64)))
                              else writeReg SCTLR2_EL1 (Mk_SCTLR2_EL1_Type (← (X_read t 64)))))))))
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
                      then writeReg SCTLR2_EL2 (Mk_SCTLR2_EL2_Type (← (X_read t 64)))
                      else writeReg SCTLR2_EL1 (Mk_SCTLR2_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SCTLR2_EL1 (Mk_SCTLR2_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR2_EL2_SysRegWrite_5e16f7d77f725c0b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg SCTLR2_EL2 (Mk_SCTLR2_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SCTLR2_EL2 (Mk_SCTLR2_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR2_EL3_SysRegWrite_78fc138b1a53fb7d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg SCTLR2_EL3 (Mk_SCTLR2_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR_EL1_SysRegWrite_1f16cf8f72a09413 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x110#12) (← (X_read t 64)))
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
              then (__set_SCTLR_EL1 (Mk_SCTLR_EL1_Type (← (X_read t 64))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (__set_SCTLR_EL1 (Mk_SCTLR_EL1_Type (← (X_read t 64))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR_EL1_SysRegWrite_82243aef3ddea2c8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_SCTLR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_SCTLR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_SCTLR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x110#12) (← (X_read t 64)))
                  else (__set_SCTLR_EL1 (Mk_SCTLR_EL1_Type (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (__set_SCTLR_EL2 (Mk_SCTLR_EL2_Type (← (X_read t 64))))
              else (__set_SCTLR_EL1 (Mk_SCTLR_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_SCTLR_EL1 (Mk_SCTLR_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR_EL2_SysRegWrite_3de2374320961a12 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (__set_SCTLR_EL2 (Mk_SCTLR_EL2_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_SCTLR_EL2 (Mk_SCTLR_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR_EL3_SysRegWrite_5a24dde2d7f68746 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg SCTLR_EL3 (Mk_SCTLR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCXTNUM_EL0_SysRegWrite_9142402a828d0db8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EnSCXT ← (( do (pure (_get_SCR_EL3_Type_EnSCXT (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCTLR_EL1_TSCXT ← (( do (pure (_get_SCTLR_EL1_Type_TSCXT (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_EnSCXT ← (( do (pure (_get_HCR_EL2_Type_EnSCXT (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_SCXTNUM_EL0 ← (( do (pure (_get_HFGWTR_EL2_Type_SCXTNUM_EL0 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_SCXTNUM_EL0 == 1#1)) : Bool)
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
                          else writeReg SCXTNUM_EL0 (← (X_read t 64))))))))
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_SCXTNUM_EL0 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_EnSCXT == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg SCXTNUM_EL0 (← (X_read t 64))))))
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
                  else writeReg SCXTNUM_EL0 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SCXTNUM_EL0 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCXTNUM_EL1_SysRegWrite_2b6dcbac83d50af9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x188#12) (← (X_read t 64)))
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
                      else writeReg SCXTNUM_EL1 (← (X_read t 64))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg SCXTNUM_EL1 (← (X_read t 64))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCXTNUM_EL2_SysRegWrite_79fa24deaac0a4f5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg SCXTNUM_EL2 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SCXTNUM_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCXTNUM_EL2_SysRegWrite_a7e8bf366cb42aa8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EnSCXT ← (( do (pure (_get_SCR_EL3_Type_EnSCXT (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_EnSCXT ← (( do (pure (_get_HCR_EL2_Type_EnSCXT (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_SCXTNUM_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_SCXTNUM_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_SCXTNUM_EL1 == 1#1)) : Bool)
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
                              then (NVMem_set (BitVec.toNat 0x188#12) (← (X_read t 64)))
                              else writeReg SCXTNUM_EL1 (← (X_read t 64))))))))
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
                      then writeReg SCXTNUM_EL2 (← (X_read t 64))
                      else writeReg SCXTNUM_EL1 (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SCXTNUM_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCXTNUM_EL3_SysRegWrite_5070eac7134cb9ba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg SCXTNUM_EL3 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SDER32_EL2_SysRegWrite_cf03546943dc260a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else writeReg SDER32_EL2 (Mk_SDER32_EL2_Type (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else writeReg SDER32_EL2 (Mk_SDER32_EL2_Type (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def SDER32_EL3_SysRegWrite_b1dc0570bf04f2cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (SDER32_EL3_write (Mk_SDER32_EL3_Type (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def SMCR_EL1_SysRegWrite_2f584a7beafe4537 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1F0#12) (← (X_read t 64)))
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
                          else writeReg SMCR_EL1 (Mk_SMCR_EL1_Type (← (X_read t 64))))))
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
                      else writeReg SMCR_EL1 (Mk_SMCR_EL1_Type (← (X_read t 64))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMCR_EL1_SysRegWrite_8e1c739345d9c5c4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              then (NVMem_set (BitVec.toNat 0x1F0#12) (← (X_read t 64)))
                              else writeReg SMCR_EL1 (Mk_SMCR_EL1_Type (← (X_read t 64)))))))))
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
                              then writeReg SMCR_EL2 (Mk_SMCR_EL2_Type (← (X_read t 64)))
                              else writeReg SMCR_EL1 (Mk_SMCR_EL1_Type (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))
                  else writeReg SMCR_EL1 (Mk_SMCR_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMCR_EL2_SysRegWrite_89c07e726ee82646 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          else writeReg SMCR_EL2 (Mk_SMCR_EL2_Type (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))
                  else writeReg SMCR_EL2 (Mk_SMCR_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMCR_EL3_SysRegWrite_f161cc4d183ca3de (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg SMCR_EL3 (Mk_SMCR_EL3_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMPRIMAP_EL2_SysRegWrite_910f2a82defe4998 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1F8#12) (← (X_read t 64)))
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
                  else writeReg SMPRIMAP_EL2 (Mk_SMPRIMAP_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg SMPRIMAP_EL2 (Mk_SMPRIMAP_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SMPRI_EL1_SysRegWrite_e2f1d7169c8f876e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_ESM ← (( do (pure (_get_CPTR_EL3_Type_ESM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nSMPRI_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_nSMPRI_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nSMPRI_EL1 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg SMPRI_EL1 (Mk_SMPRI_EL1_Type (← (X_read t 64))))))
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
                  else writeReg SMPRI_EL1 (Mk_SMPRI_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else writeReg SMPRI_EL1 (Mk_SMPRI_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMACCESSR_EL1_SysRegWrite_6eda6cd61ef5c926 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x8E8#12) (← (X_read t 64)))
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
                      else writeReg SPMACCESSR_EL1 (Mk_SPMACCESSR_EL1_Type (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg SPMACCESSR_EL1 (Mk_SPMACCESSR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMACCESSR_EL1_SysRegWrite_f6ec7d62f3c86b85 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMACCESSR_EL1 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMACCESSR_EL1 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMACCESSR_EL1 == 0#1)) : Bool)
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
                              then (NVMem_set (BitVec.toNat 0x8E8#12) (← (X_read t 64)))
                              else writeReg SPMACCESSR_EL1 (Mk_SPMACCESSR_EL1_Type (← (X_read t 64)))))))))
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
                      then writeReg SPMACCESSR_EL2 (Mk_SPMACCESSR_EL2_Type (← (X_read t 64)))
                      else writeReg SPMACCESSR_EL1 (Mk_SPMACCESSR_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SPMACCESSR_EL1 (Mk_SPMACCESSR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMACCESSR_EL2_SysRegWrite_5752c6190c2458e4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg SPMACCESSR_EL2 (Mk_SPMACCESSR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SPMACCESSR_EL2 (Mk_SPMACCESSR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMACCESSR_EL3_SysRegWrite_01596d02a5af2d0d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg SPMACCESSR_EL3 (Mk_SPMACCESSR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: s : Int -/
def SPMCNTENCLR_EL0_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: s : Int -/
def SPMCNTENSET_EL0_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: s : Int -/
def SPMCR_EL0_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: n : Int, s : Int -/
def SPMEVCNTR_EL0_set (s : Int) (n : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: n : Int, s : Int -/
def SPMEVFILT2R_EL0_set (s : Int) (n : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: n : Int, s : Int -/
def SPMEVFILTR_EL0_set (s : Int) (n : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: n : Int, s : Int -/
def SPMEVTYPER_EL0_set (s : Int) (n : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: s : Int -/
def SPMINTENCLR_EL1_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: s : Int -/
def SPMINTENSET_EL1_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: s : Int -/
def SPMOVSCLR_EL0_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: s : Int -/
def SPMOVSSET_EL0_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: s : Int -/
def SPMROOTCR_EL3_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: s : Int -/
def SPMSCR_EL1_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: t : Int -/
def SPMSELR_EL0_SysRegWrite_3811b80bc21b4614 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMSELR_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMSELR_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMSELR_EL0 == 0#1)) : Bool)
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
                          else writeReg SPMSELR_EL0 (Mk_SPMSELR_EL0_Type (← (X_read t 64)))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMSELR_EL0 == 0#1)) : Bool)
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
                          else writeReg SPMSELR_EL0 (Mk_SPMSELR_EL0_Type (← (X_read t 64))))))))
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
                  else writeReg SPMSELR_EL0 (Mk_SPMSELR_EL0_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SPMSELR_EL0 (Mk_SPMSELR_EL0_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_EL1_SysRegWrite_f71c6fe811b4fd71 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x160#12) (← (X_read t 64)))
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
              then writeReg SPSR_EL1 (Mk_SPSR_EL1_Type (← (X_read t 64)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg SPSR_EL1 (Mk_SPSR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_EL2_SysRegWrite_5e3ca78864ff5189 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg SPSR_EL1 (Mk_SPSR_EL1_Type (← (X_read t 64)))
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
              else writeReg SPSR_EL2 (Mk_SPSR_EL2_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SPSR_EL2 (Mk_SPSR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_EL2_SysRegWrite_abd009a999e4a431 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (NVMem_set (BitVec.toNat 0x160#12) (← (X_read t 64)))
                  else writeReg SPSR_EL1 (Mk_SPSR_EL1_Type (← (X_read t 64))))))
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
                  then writeReg SPSR_EL2 (Mk_SPSR_EL2_Type (← (X_read t 64)))
                  else writeReg SPSR_EL1 (Mk_SPSR_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SPSR_EL1 (Mk_SPSR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_EL3_SysRegWrite_456470f5b76b34d3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg SPSR_EL3 (Mk_SPSR_EL3_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_abt_SysRegWrite_fcfb847bea953cff (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg SPSR_abt (Mk_SPSR_abt_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SPSR_abt (Mk_SPSR_abt_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_fiq_SysRegWrite_2563b670f1657883 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg SPSR_fiq (Mk_SPSR_fiq_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SPSR_fiq (Mk_SPSR_fiq_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_irq_SysRegWrite_ce481d2491908c8e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg SPSR_irq (Mk_SPSR_irq_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SPSR_irq (Mk_SPSR_irq_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSR_und_SysRegWrite_684160009ec60b5e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg SPSR_und (Mk_SPSR_und_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SPSR_und (Mk_SPSR_und_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPSel_SysRegWrite_0f30d004facde41d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with SP := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 0)]))) }
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with SP := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 0)]))) }
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg PSTATE { (← readReg PSTATE) with SP := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 0)]))) }
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SP_EL0_SysRegWrite_eb3954d261630177 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          else writeReg SP_EL0 (← (X_read t 64)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__PSTATE_SP == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else writeReg SP_EL0 (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__PSTATE_SP == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg SP_EL0 (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SP_EL1_SysRegWrite_ef3afaab001d7071 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x240#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg SP_EL1 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SP_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SP_EL2_SysRegWrite_ff905d2134243823 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg SP_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SSBS_SysRegWrite_9913e9eaee3498e8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with SSBS := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 12)]))) }
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with SSBS := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 12)]))) }
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with SSBS := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 12)]))) }
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg PSTATE { (← readReg PSTATE) with SSBS := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 12)]))) }
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SVCR_SysRegWrite_6af153139ced98f4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          else (SetPSTATE_SVCR (← (X_read t 32)))))))))
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
                          else (SetPSTATE_SVCR (← (X_read t 32))))))))
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
                          else (SetPSTATE_SVCR (← (X_read t 32)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))
                  else (SetPSTATE_SVCR (← (X_read t 32))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCO_SysRegWrite_ad1525aaa3fbe60d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with TCO := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 25)]))) }
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with TCO := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 25)]))) }
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with TCO := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 25)]))) }
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg PSTATE { (← readReg PSTATE) with TCO := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 25)]))) }
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR2_EL1_SysRegWrite_8d0ce9228b7cb5c8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x270#12) (← (X_read t 64)))
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
                      else writeReg TCR2_EL1 (Mk_TCR2_EL1_Type (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg TCR2_EL1 (Mk_TCR2_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR2_EL2_SysRegWrite_61260f52329ef360 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg TCR2_EL2 (Mk_TCR2_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TCR2_EL2 (Mk_TCR2_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR2_EL2_SysRegWrite_c04bf19f053d56ef (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_TCR2En ← (( do (pure (_get_SCR_EL3_Type_TCR2En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_TCR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_TCR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if (((← (EL2Enabled ())) && (__HCR_EL2_TVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TCR_EL1 == 1#1)) : Bool)
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
                              then (NVMem_set (BitVec.toNat 0x270#12) (← (X_read t 64)))
                              else writeReg TCR2_EL1 (Mk_TCR2_EL1_Type (← (X_read t 64)))))))))
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
                      then writeReg TCR2_EL2 (Mk_TCR2_EL2_Type (← (X_read t 64)))
                      else writeReg TCR2_EL1 (Mk_TCR2_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TCR2_EL1 (Mk_TCR2_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR_EL1_SysRegWrite_57810e368d8276c0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x120#12) (← (X_read t 64)))
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
              then writeReg TCR_EL1 (Mk_TCR_EL1_Type (← (X_read t 64)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg TCR_EL1 (Mk_TCR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR_EL1_SysRegWrite_97ed30db0464410e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_TCR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_TCR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TCR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x120#12) (← (X_read t 64)))
                  else writeReg TCR_EL1 (Mk_TCR_EL1_Type (← (X_read t 64))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg TCR_EL2 (Mk_TCR_EL2_Type (← (X_read t 64)))
              else writeReg TCR_EL1 (Mk_TCR_EL1_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TCR_EL1 (Mk_TCR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR_EL2_SysRegWrite_6c45c215eb6ac9ec (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg TCR_EL2 (Mk_TCR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TCR_EL2 (Mk_TCR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCR_EL3_SysRegWrite_7cd20b115677d482 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg TCR_EL3 (Mk_TCR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TFSRE0_EL1_SysRegWrite_c83d8537b51ba0c0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg TFSRE0_EL1 (Mk_TFSRE0_EL1_Type (← (X_read t 64))))))
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
                  else writeReg TFSRE0_EL1 (Mk_TFSRE0_EL1_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TFSRE0_EL1 (Mk_TFSRE0_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TFSR_EL1_SysRegWrite_ff5023e822575c45 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x190#12) (← (X_read t 64)))
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
                      else writeReg TFSR_EL1 (Mk_TFSR_EL1_Type (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg TFSR_EL1 (Mk_TFSR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TFSR_EL2_SysRegWrite_0de052c6a803cdd2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else writeReg TFSR_EL1 (Mk_TFSR_EL1_Type (← (X_read t 64))))))
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
                  else writeReg TFSR_EL2 (Mk_TFSR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TFSR_EL2 (Mk_TFSR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TFSR_EL2_SysRegWrite_e50f9758a2aeae18 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          then (NVMem_set (BitVec.toNat 0x190#12) (← (X_read t 64)))
                          else writeReg TFSR_EL1 (Mk_TFSR_EL1_Type (← (X_read t 64))))))))
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
                      then writeReg TFSR_EL2 (Mk_TFSR_EL2_Type (← (X_read t 64)))
                      else writeReg TFSR_EL1 (Mk_TFSR_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TFSR_EL1 (Mk_TFSR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TFSR_EL3_SysRegWrite_f3f90e5ae77101da (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg TFSR_EL3 (Mk_TFSR_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDR2_EL0_SysRegWrite_6f661a4b0c2ce1c0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EnTP2 ← (( do (pure (_get_SCR_EL3_Type_EnTP2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCTLR_EL1_EnTP2 ← (( do (pure (_get_SCTLR_EL1_Type_EnTP2 (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_EnTP2 ← (( do (pure (_get_SCTLR_EL2_Type_EnTP2 (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nTPIDR2_EL0 ← (( do (pure (_get_HFGWTR_EL2_Type_nTPIDR2_EL0 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nTPIDR2_EL0 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_EnTP2 == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else writeReg TPIDR2_EL0 (← (X_read t 64)))))))
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nTPIDR2_EL0 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_EnTP2 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else writeReg TPIDR2_EL0 (← (X_read t 64)))))
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
                  else writeReg TPIDR2_EL0 (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TPIDR2_EL0 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDRRO_EL0_SysRegWrite_7203698352c87d5e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_TPIDRRO_EL0 ← (( do (pure (_get_HFGWTR_EL2_Type_TPIDRRO_EL0 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TPIDRRO_EL0 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else writeReg TPIDRRO_EL0 (← (X_read t 64)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg TPIDRRO_EL0 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TPIDRRO_EL0 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDR_EL0_SysRegWrite_0cc7097850c46a2a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_TPIDR_EL0 ← (( do (pure (_get_HFGWTR_EL2_Type_TPIDR_EL0 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TPIDR_EL0 == 1#1)) : Bool)
      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
      else writeReg TPIDR_EL0 (← (X_read t 64)))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TPIDR_EL0 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else writeReg TPIDR_EL0 (← (X_read t 64)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg TPIDR_EL0 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TPIDR_EL0 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDR_EL1_SysRegWrite_be51f1ab4eeaabd3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_TPIDR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_TPIDR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TPIDR_EL1 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else writeReg TPIDR_EL1 (← (X_read t 64)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg TPIDR_EL1 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TPIDR_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDR_EL2_SysRegWrite_6e0625002baa042c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x090#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg TPIDR_EL2 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TPIDR_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDR_EL3_SysRegWrite_ea00df52cbaac80c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg TPIDR_EL3 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TRFCR_EL1_SysRegWrite_cc3bca184cf88f2f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x880#12) (← (X_read t 64)))
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
                      else writeReg TRFCR_EL1 (Mk_TRFCR_EL1_Type (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg TRFCR_EL1 (Mk_TRFCR_EL1_Type (← (X_read t 64)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TRFCR_EL2_SysRegWrite_20a366481946c8fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg TRFCR_EL2 (Mk_TRFCR_EL2_Type (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TRFCR_EL2 (Mk_TRFCR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TRFCR_EL2_SysRegWrite_75efd6fa24ddc2b7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TTRF ← (( do (pure (_get_MDCR_EL3_Type_TTRF (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_TRFCR_EL1 ← (( do (pure (_get_HDFGWTR_EL2_Type_TRFCR_EL1 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_TRFCR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
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
                          then (NVMem_set (BitVec.toNat 0x880#12) (← (X_read t 64)))
                          else writeReg TRFCR_EL1 (Mk_TRFCR_EL1_Type (← (X_read t 64))))))))
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
                      then writeReg TRFCR_EL2 (Mk_TRFCR_EL2_Type (← (X_read t 64)))
                      else writeReg TRFCR_EL1 (Mk_TRFCR_EL1_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TRFCR_EL1 (Mk_TRFCR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR0_EL1_SysRegWrite_1418275ded3dcceb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x200#12) (← (X_read t 64)))
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
              then (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL1_read ())) 63 0 (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL1_read ())) 63 0 (← (X_read t 64)))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR0_EL2_SysRegWrite_4eaec85b078ecd3b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_TTBR0_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_TTBR0_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TTBR0_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x200#12) (← (X_read t 64)))
                  else (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL1_read ())) 63 0 (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (TTBR0_EL2_write (Mk_TTBR0_EL2_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL2_read ())) 63 0 (← (X_read t 64)))))
              else (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL1_read ())) 63 0 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL1_read ())) 63 0 (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR0_EL2_SysRegWrite_6f2504a3aff125cc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (TTBR0_EL2_write (Mk_TTBR0_EL2_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL2_read ())) 63 0 (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (TTBR0_EL2_write (Mk_TTBR0_EL2_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL2_read ())) 63 0 (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR0_EL3_SysRegWrite_3f52a3edf2b13467 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg TTBR0_EL3 (Mk_TTBR0_EL3_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR1_EL1_SysRegWrite_4d156e352c93f29e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x210#12) (← (X_read t 64)))
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
              then (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR1_EL1_read ())) 63 0 (← (X_read t 64)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR1_EL1_read ())) 63 0 (← (X_read t 64)))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR1_EL1_SysRegWrite_949dc27ace2a7dbe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_TTBR1_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_TTBR1_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TTBR1_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x210#12) (← (X_read t 64)))
                  else (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR1_EL1_read ())) 63 0 (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange (← readReg TTBR1_EL2) 63 0 (← (X_read t 64)))
              else (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR1_EL1_read ())) 63 0 (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR1_EL1_read ())) 63 0 (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR1_EL2_SysRegWrite_2b203badd6cd49c7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange (← readReg TTBR1_EL2) 63 0 (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange (← readReg TTBR1_EL2) 63 0 (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def UAO_SysRegWrite_3265e241e210a049 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with UAO := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 23)]))) }
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with UAO := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 23)]))) }
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg PSTATE { (← readReg PSTATE) with UAO := ← (do (pure (BitVec.join1 [(BitVec.access (← (X_read t 64)) 23)]))) }
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VBAR_EL1_SysRegWrite_2545adf6b767cca1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x250#12) (← (X_read t 64)))
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
              then writeReg VBAR_EL1 (← (X_read t 64))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then writeReg VBAR_EL1 (← (X_read t 64))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VBAR_EL2_SysRegWrite_58cf9956b761a13c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_VBAR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_VBAR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_VBAR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (NVMem_set (BitVec.toNat 0x250#12) (← (X_read t 64)))
                  else writeReg VBAR_EL1 (← (X_read t 64)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then writeReg VBAR_EL2 (← (X_read t 64))
              else writeReg VBAR_EL1 (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg VBAR_EL1 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VBAR_EL2_SysRegWrite_89ae3d074e337e2e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg VBAR_EL2 (← (X_read t 64))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg VBAR_EL2 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VBAR_EL3_SysRegWrite_a4ea3bd6f4a6393d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then writeReg VBAR_EL3 (← (X_read t 64))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VDISR_EL2_SysRegWrite_22757a602e967277 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then writeReg VDISR_EL2 (Mk_VDISR_EL2_Type (← (X_read t 64)))
          else
            (do
              if (((←((pure (HaveEL EL3)) <&&> (do
                     (pure (! (← (Halted ()))))))) && (__SCR_EL3_EA == 1#1)) : Bool)
              then (pure ())
              else writeReg DISR_EL1 (Mk_DISR_EL1_Type (← (X_read t 64)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (HaveEL EL3)) <&&> (do
                     (pure (! (← (Halted ()))))))) && (__SCR_EL3_EA == 1#1)) : Bool)
              then (pure ())
              else writeReg DISR_EL1 (Mk_DISR_EL1_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg DISR_EL1 (Mk_DISR_EL1_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VDISR_EL2_SysRegWrite_d4de228de4dce7ee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x500#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg VDISR_EL2 (Mk_VDISR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg VDISR_EL2 (Mk_VDISR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VMECID_A_EL2_SysRegWrite_d4d52ce2ee2e86c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else writeReg VMECID_A_EL2 (Mk_VMECID_A_EL2_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg VMECID_A_EL2 (Mk_VMECID_A_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VMECID_P_EL2_SysRegWrite_b0549714107a13fc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else writeReg VMECID_P_EL2 (Mk_VMECID_P_EL2_Type (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg VMECID_P_EL2 (Mk_VMECID_P_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VMPIDR_EL2_SysRegWrite_652dff4d193b16d2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x050#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg VMPIDR_EL2 (Mk_VMPIDR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (pure ())
                  else writeReg VMPIDR_EL2 (Mk_VMPIDR_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VNCR_EL2_SysRegWrite_4acc113d8c83cbf3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x0B0#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg VNCR_EL2 (Mk_VNCR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg VNCR_EL2 (Mk_VNCR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VPIDR_EL2_SysRegWrite_8d6e5569c8c164cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x088#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg VPIDR_EL2 (Mk_VPIDR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (pure ())
                  else writeReg VPIDR_EL2 (Mk_VPIDR_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VSESR_EL2_SysRegWrite_9e724bce6c5a8288 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x508#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg VSESR_EL2 (Mk_VSESR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg VSESR_EL2 (Mk_VSESR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VSTCR_EL2_SysRegWrite_9398e11d9c39d020 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (NVMem_set (BitVec.toNat 0x048#12) (← (X_read t 64)))
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
              else writeReg VSTCR_EL2 (Mk_VSTCR_EL2_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg VSTCR_EL2 (Mk_VSTCR_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VSTTBR_EL2_SysRegWrite_313d4b469c28863c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (NVMem_set (BitVec.toNat 0x030#12) (← (X_read t 64)))
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
              else writeReg VSTTBR_EL2 (Mk_VSTTBR_EL2_Type (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg VSTTBR_EL2 (Mk_VSTTBR_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VTCR_EL2_SysRegWrite_087e5f2e2721566e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x040#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then writeReg VTCR_EL2 (Mk_VTCR_EL2_Type (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg VTCR_EL2 (Mk_VTCR_EL2_Type (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VTTBR_EL2_SysRegWrite_e5049cda9fc04134 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x020#12) (← (X_read t 64)))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (VTTBR_EL2_write (Mk_VTTBR_EL2_Type (Sail.BitVec.updateSubrange (← (VTTBR_EL2_read ())) 63 0 (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (VTTBR_EL2_write (Mk_VTTBR_EL2_Type (Sail.BitVec.updateSubrange (← (VTTBR_EL2_read ())) 63 0 (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ZCR_EL1_SysRegWrite_28a1dc91762b9c5d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              then (NVMem_set (BitVec.toNat 0x1E0#12) (← (X_read t 64)))
                              else writeReg ZCR_EL1 (Mk_ZCR_EL1_Type (← (X_read t 64)))))))))
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
                              then writeReg ZCR_EL2 (Mk_ZCR_EL2_Type (← (X_read t 64)))
                              else writeReg ZCR_EL1 (Mk_ZCR_EL1_Type (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_EZ == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8))
                  else writeReg ZCR_EL1 (Mk_ZCR_EL1_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ZCR_EL1_SysRegWrite_8900d1c129d0830f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (NVMem_set (BitVec.toNat 0x1E0#12) (← (X_read t 64)))
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
                          else writeReg ZCR_EL1 (Mk_ZCR_EL1_Type (← (X_read t 64))))))
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
                      else writeReg ZCR_EL1 (Mk_ZCR_EL1_Type (← (X_read t 64))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ZCR_EL2_SysRegWrite_bd0a9b879ec59921 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          else writeReg ZCR_EL2 (Mk_ZCR_EL2_Type (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_EZ == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8))
                  else writeReg ZCR_EL2 (Mk_ZCR_EL2_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ZCR_EL3_SysRegWrite_8b6f2f3c0ab9da70 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg ZCR_EL3 (Mk_ZCR_EL3_Type (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S12E0R_SysOpsWrite_0c5b1bd4a1d08392 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then
            (do
              if ((←((pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)) <||> (do
                   (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) == 0b00#2))))) : Bool)
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Read)
              else (AArch64_AT (← (X_read t 64)) TranslationStage_12 EL0 ATAccess_Read))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Read)
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)) <||> (do
                             (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) == 0b00#2)))))) : Bool)
                      then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Read)
                      else (AArch64_AT (← (X_read t 64)) TranslationStage_12 EL0 ATAccess_Read)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S12E0W_SysOpsWrite_ebaedef9bc851c96 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then
            (do
              if ((←((pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)) <||> (do
                   (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) == 0b00#2))))) : Bool)
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Write)
              else (AArch64_AT (← (X_read t 64)) TranslationStage_12 EL0 ATAccess_Write))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Write)
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)) <||> (do
                             (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) == 0b00#2)))))) : Bool)
                      then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Write)
                      else (AArch64_AT (← (X_read t 64)) TranslationStage_12 EL0 ATAccess_Write)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S12E1R_SysOpsWrite_90c7bc3b4c4e8ad2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then
            (do
              if ((←((pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)) <||> (do
                   (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) == 0b00#2))))) : Bool)
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Read)
              else (AArch64_AT (← (X_read t 64)) TranslationStage_12 EL1 ATAccess_Read))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Read)
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)) <||> (do
                             (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) == 0b00#2)))))) : Bool)
                      then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Read)
                      else (AArch64_AT (← (X_read t 64)) TranslationStage_12 EL1 ATAccess_Read)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S12E1W_SysOpsWrite_1152e7884348cb33 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then
            (do
              if ((←((pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)) <||> (do
                   (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) == 0b00#2))))) : Bool)
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Write)
              else (AArch64_AT (← (X_read t 64)) TranslationStage_12 EL1 ATAccess_Write))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Write)
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)) <||> (do
                             (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) == 0b00#2)))))) : Bool)
                      then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Write)
                      else (AArch64_AT (← (X_read t 64)) TranslationStage_12 EL1 ATAccess_Write)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S1E0R_SysOpsWrite_40187a824e445931 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_AT ← (( do (pure (_get_HCR_EL2_Type_AT (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_ATS1E0R ← (( do (pure (_get_HFGITR_EL2_Type_ATS1E0R (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_AT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_ATS1E0R == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Read)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Read)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Read)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S1E0W_SysOpsWrite_5d5981498f3ff63f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_AT ← (( do (pure (_get_HCR_EL2_Type_AT (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_ATS1E0W ← (( do (pure (_get_HFGITR_EL2_Type_ATS1E0W (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_AT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_ATS1E0W == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Write)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Write)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL0 ATAccess_Write)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S1E1RP_SysOpsWrite_597c8bbb547c9cc7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_AT ← (( do (pure (_get_HCR_EL2_Type_AT (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_ATS1E1RP ← (( do (pure (_get_HFGITR_EL2_Type_ATS1E1RP (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_AT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_ATS1E1RP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_ReadPAN)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_ReadPAN)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_ReadPAN)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S1E1R_SysOpsWrite_efb944f010174dbe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_AT ← (( do (pure (_get_HCR_EL2_Type_AT (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_ATS1E1R ← (( do (pure (_get_HFGITR_EL2_Type_ATS1E1R (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_AT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_ATS1E1R == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Read)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Read)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Read)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S1E1WP_SysOpsWrite_56bf9c5f4fdf95fa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_AT ← (( do (pure (_get_HCR_EL2_Type_AT (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_ATS1E1WP ← (( do (pure (_get_HFGITR_EL2_Type_ATS1E1WP (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_AT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_ATS1E1WP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_WritePAN)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_WritePAN)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_WritePAN)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S1E1W_SysOpsWrite_97fd2fc3596f8e01 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_AT ← (( do (pure (_get_HCR_EL2_Type_AT (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_ATS1E1W ← (( do (pure (_get_HFGITR_EL2_Type_ATS1E1W (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_AT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_ATS1E1W == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Write)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Write)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL1 ATAccess_Write)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S1E2R_SysOpsWrite_759b68e4499a5900 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL2 ATAccess_Read)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL2 ATAccess_Read))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S1E2W_SysOpsWrite_f45a5d407163b4bd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL2 ATAccess_Write)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL2 ATAccess_Write))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S1E3R_SysOpsWrite_260837ba334806bd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL3 ATAccess_Read)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AT_S1E3W_SysOpsWrite_6d38ab8c7cb15a2d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_AT (← (X_read t 64)) TranslationStage_1 EL3 ATAccess_Write)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRB_IALL_SysOpsWrite_dd273770082db6a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_nBRBIALL ← (( do (pure (_get_HFGITR_EL2_Type_nBRBIALL (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_nBRBIALL == 0#1)) : Bool)
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
                          else (BRB_IALL ()))))))
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
                          else (BRB_IALL ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (BRB_IALL ())
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRB_INJ_SysOpsWrite_9a0dba3ea5bd7523 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_nBRBINJ ← (( do (pure (_get_HFGITR_EL2_Type_nBRBINJ (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_nBRBINJ == 0#1)) : Bool)
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
                          else (BRB_INJ ()))))))
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
                          else (BRB_INJ ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (BRB_INJ ())
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CFP_RCTX_SysOpsWrite_c7a3d5c0c069ede1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_EnRCTX ← (( do (pure (_get_SCTLR_EL1_Type_EnRCTX (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_CFPRCTX ← (( do (pure (_get_HFGITR_EL2_Type_CFPRCTX (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_EnRCTX ← (( do (pure (_get_SCTLR_EL2_Type_EnRCTX (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_EnRCTX == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_CFPRCTX == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_EnRCTX == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_ControlFlow))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_CFPRCTX == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_ControlFlow)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_ControlFlow)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_ControlFlow)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def COSP_RCTX_SysOpsWrite_575f6b74afb13f3b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_EnRCTX ← (( do (pure (_get_SCTLR_EL1_Type_EnRCTX (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_COSPRCTX ← (( do (pure (_get_HFGITR_EL2_Type_COSPRCTX (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_EnRCTX ← (( do (pure (_get_SCTLR_EL2_Type_EnRCTX (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_EnRCTX == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_COSPRCTX == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_EnRCTX == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_Other))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_COSPRCTX == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_Other)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_Other)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_Other)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPP_RCTX_SysOpsWrite_40a73711d28892b9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_EnRCTX ← (( do (pure (_get_SCTLR_EL1_Type_EnRCTX (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_CPPRCTX ← (( do (pure (_get_HFGITR_EL2_Type_CPPRCTX (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_EnRCTX ← (( do (pure (_get_SCTLR_EL2_Type_EnRCTX (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_EnRCTX == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_CPPRCTX == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_EnRCTX == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_CachePrefetch))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_CPPRCTX == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_CachePrefetch)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_CachePrefetch)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_CachePrefetch)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CGDSW_SysOpsWrite_928589dc16baf135 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TSW ← (( do (pure (_get_HCR_EL2_Type_TSW (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCSW ← (( do (pure (_get_HFGITR_EL2_Type_DCCSW (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TSW == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCSW == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_SetWay)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_SetWay)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_SetWay)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CGDVAC_SysOpsWrite_ec22b0e1f02114c3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCVAC ← (( do (pure (_get_HFGITR_EL2_Type_DCCVAC (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoC)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoC)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoC)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoC)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CGDVADP_SysOpsWrite_8e52ffae1d90dad3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCVADP ← (( do (pure (_get_HFGITR_EL2_Type_DCCVADP (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVADP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoDP)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVADP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoDP)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoDP)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoDP)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CGDVAP_SysOpsWrite_341059a5c0ebf49f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCVAP ← (( do (pure (_get_HFGITR_EL2_Type_DCCVAP (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoP)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoP)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoP)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoP)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CGSW_SysOpsWrite_1f93959761278ed4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TSW ← (( do (pure (_get_HCR_EL2_Type_TSW (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCSW ← (( do (pure (_get_HFGITR_EL2_Type_DCCSW (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TSW == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCSW == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_SetWay)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_SetWay)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_SetWay)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CGVAC_SysOpsWrite_c31db9a0c232aa17 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCVAC ← (( do (pure (_get_HFGITR_EL2_Type_DCCVAC (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoC)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoC)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoC)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoC)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CGVADP_SysOpsWrite_6e93030bf0a27352 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCVADP ← (( do (pure (_get_HFGITR_EL2_Type_DCCVADP (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVADP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoDP)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVADP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoDP)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoDP)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoDP)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CGVAP_SysOpsWrite_884677eb0934135e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCVAP ← (( do (pure (_get_HFGITR_EL2_Type_DCCVAP (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoP)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoP)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoP)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Clean CacheOpScope_PoP)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CIGDPAE_SysOpsWrite_8bfd8283adbf50a4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then
            (do
              if ((! (← (IsCurrentSecurityState SS_Realm))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_PoE))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_PoE)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CIGDPAPA_SysOpsWrite_04c6858387bf2414 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (pure (DC_CIGDPAPA (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CIGDSW_SysOpsWrite_b520ae0cd5c0ff01 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TSW ← (( do (pure (_get_HCR_EL2_Type_TSW (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCISW ← (( do (pure (_get_HFGITR_EL2_Type_DCCISW (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TSW == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCISW == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_SetWay)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_SetWay)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_SetWay)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CIGDVAC_SysOpsWrite_2ef9f271e7e2809f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCIVAC ← (( do (pure (_get_HFGITR_EL2_Type_DCCIVAC (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCIVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_PoC)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCIVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_PoC)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_PoC)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_PoC)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CIGSW_SysOpsWrite_72fc6e114637ba18 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TSW ← (( do (pure (_get_HCR_EL2_Type_TSW (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCISW ← (( do (pure (_get_HFGITR_EL2_Type_DCCISW (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TSW == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCISW == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_CleanInvalidate CacheOpScope_SetWay)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_CleanInvalidate CacheOpScope_SetWay)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_CleanInvalidate CacheOpScope_SetWay)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CIGVAC_SysOpsWrite_8404661bd642a412 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCIVAC ← (( do (pure (_get_HFGITR_EL2_Type_DCCIVAC (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCIVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_CleanInvalidate CacheOpScope_PoC)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCIVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_CleanInvalidate CacheOpScope_PoC)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_CleanInvalidate CacheOpScope_PoC)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_CleanInvalidate CacheOpScope_PoC)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CIPAE_SysOpsWrite_ab72a0dcf6c65302 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then
            (do
              if ((! (← (IsCurrentSecurityState SS_Realm))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_CleanInvalidate CacheOpScope_PoE))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_CleanInvalidate CacheOpScope_PoE)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CIPAPA_SysOpsWrite_bec4067ecaf3ce6b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (pure (DC_CIPAPA (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CISW_SysOpsWrite_b065e0cdcdd8276d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TSW ← (( do (pure (_get_HCR_EL2_Type_TSW (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCISW ← (( do (pure (_get_HFGITR_EL2_Type_DCCISW (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TSW == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCISW == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_CleanInvalidate CacheOpScope_SetWay)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_CleanInvalidate CacheOpScope_SetWay)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_CleanInvalidate CacheOpScope_SetWay)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CIVAC_SysOpsWrite_aa1291714e4724c8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCIVAC ← (( do (pure (_get_HFGITR_EL2_Type_DCCIVAC (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCIVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_CleanInvalidate CacheOpScope_PoC)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCIVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_CleanInvalidate CacheOpScope_PoC)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_CleanInvalidate CacheOpScope_PoC)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_CleanInvalidate CacheOpScope_PoC)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CSW_SysOpsWrite_5e3c21c77aa230fd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TSW ← (( do (pure (_get_HCR_EL2_Type_TSW (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCSW ← (( do (pure (_get_HFGITR_EL2_Type_DCCSW (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TSW == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCSW == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_SetWay)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_SetWay)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_SetWay)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CVAC_SysOpsWrite_a3e7839db596aa73 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCVAC ← (( do (pure (_get_HFGITR_EL2_Type_DCCVAC (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoC)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoC)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoC)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoC)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CVADP_SysOpsWrite_2fe8e7b346963113 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCVADP ← (( do (pure (_get_HFGITR_EL2_Type_DCCVADP (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVADP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoDP)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVADP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoDP)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoDP)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoDP)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CVAP_SysOpsWrite_6979d303ac43aa55 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCVAP ← (( do (pure (_get_HFGITR_EL2_Type_DCCVAP (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoP)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoP)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoP)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoP)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_CVAU_SysOpsWrite_994be56e554e4f7c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPU ← (( do (pure (_get_HCR_EL2_Type_TPU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TOCU ← (( do (pure (_get_HCR_EL2_Type_TOCU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCCVAU ← (( do (pure (_get_HFGITR_EL2_Type_DCCVAU (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPU == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TOCU == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAU == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoU))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPU == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TOCU == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCCVAU == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoU))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoU)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Clean CacheOpScope_PoU)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_GVA_SysOpsWrite_26c60f1734aa9835 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_DZE ← (( do (pure (_get_SCTLR_EL1_Type_DZE (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TDZ ← (( do (pure (_get_HCR_EL2_Type_TDZ (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCZVA ← (( do (pure (_get_HFGITR_EL2_Type_DCZVA (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_DZE ← (( do (pure (_get_SCTLR_EL2_Type_DZE (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_DZE == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TDZ == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCZVA == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_DZE == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_MemZero (← (X_read t 64)) CacheType_Tag)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TDZ == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCZVA == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_MemZero (← (X_read t 64)) CacheType_Tag)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_MemZero (← (X_read t 64)) CacheType_Tag)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_MemZero (← (X_read t 64)) CacheType_Tag)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_GZVA_SysOpsWrite_6a4bc458b38a36cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_DZE ← (( do (pure (_get_SCTLR_EL1_Type_DZE (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TDZ ← (( do (pure (_get_HCR_EL2_Type_TDZ (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCZVA ← (( do (pure (_get_HFGITR_EL2_Type_DCZVA (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_DZE ← (( do (pure (_get_SCTLR_EL2_Type_DZE (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_DZE == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TDZ == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCZVA == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_DZE == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_MemZero (← (X_read t 64)) CacheType_Data_Tag)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TDZ == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCZVA == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_MemZero (← (X_read t 64)) CacheType_Data_Tag)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_MemZero (← (X_read t 64)) CacheType_Data_Tag)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_MemZero (← (X_read t 64)) CacheType_Data_Tag)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_IGDSW_SysOpsWrite_ad0a1d536c426f1f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TSW ← (( do (pure (_get_HCR_EL2_Type_TSW (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCISW ← (( do (pure (_get_HFGITR_EL2_Type_DCISW (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TSW == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCISW == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_SetWay)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_SetWay)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_SetWay)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_IGDVAC_SysOpsWrite_2b2dc8b1efa4218a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCIVAC ← (( do (pure (_get_HFGITR_EL2_Type_DCIVAC (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCIVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_PoC)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_PoC)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_PoC)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_IGSW_SysOpsWrite_b40e0b982eab4603 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TSW ← (( do (pure (_get_HCR_EL2_Type_TSW (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCISW ← (( do (pure (_get_HFGITR_EL2_Type_DCISW (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TSW == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCISW == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Invalidate CacheOpScope_SetWay)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Invalidate CacheOpScope_SetWay)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Invalidate CacheOpScope_SetWay)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_IGVAC_SysOpsWrite_79e5a655957681f5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCIVAC ← (( do (pure (_get_HFGITR_EL2_Type_DCIVAC (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCIVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Invalidate CacheOpScope_PoC)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Invalidate CacheOpScope_PoC)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Tag CacheOp_Invalidate CacheOpScope_PoC)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_ISW_SysOpsWrite_d415f7441de61c87 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TSW ← (( do (pure (_get_HCR_EL2_Type_TSW (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCISW ← (( do (pure (_get_HFGITR_EL2_Type_DCISW (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TSW == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCISW == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Invalidate CacheOpScope_SetWay)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Invalidate CacheOpScope_SetWay)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Invalidate CacheOpScope_SetWay)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_IVAC_SysOpsWrite_9a59a62370daa1c9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TPCP ← (( do (pure (_get_HCR_EL2_Type_TPCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCIVAC ← (( do (pure (_get_HFGITR_EL2_Type_DCIVAC (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCIVAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Invalidate CacheOpScope_PoC)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Invalidate CacheOpScope_PoC)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_DC (← (X_read t 64)) CacheType_Data CacheOp_Invalidate CacheOpScope_PoC)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DC_ZVA_SysOpsWrite_4df78ae16ed9b1bc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_DZE ← (( do (pure (_get_SCTLR_EL1_Type_DZE (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TDZ ← (( do (pure (_get_HCR_EL2_Type_TDZ (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DCZVA ← (( do (pure (_get_HFGITR_EL2_Type_DCZVA (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_DZE ← (( do (pure (_get_SCTLR_EL2_Type_DZE (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_DZE == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TDZ == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCZVA == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_DZE == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_MemZero (← (X_read t 64)) CacheType_Data)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TDZ == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DCZVA == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_MemZero (← (X_read t 64)) CacheType_Data)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_MemZero (← (X_read t 64)) CacheType_Data)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_MemZero (← (X_read t 64)) CacheType_Data)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DVP_RCTX_SysOpsWrite_a4d7cddd32aa439c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_EnRCTX ← (( do (pure (_get_SCTLR_EL1_Type_EnRCTX (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_DVPRCTX ← (( do (pure (_get_HFGITR_EL2_Type_DVPRCTX (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_EnRCTX ← (( do (pure (_get_SCTLR_EL2_Type_EnRCTX (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_EnRCTX == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if ((((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DVPRCTX == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_EnRCTX == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_DataValue))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_DVPRCTX == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_DataValue)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_DataValue)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_RestrictPrediction (← (X_read t 64)) RestrictType_DataValue)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPOPCX_SysOpsWrite_8b33b35a7177cc05 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_EXLOCK ← (( do (pure (← readReg PSTATE).EXLOCK) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_nGCSEPP ← (( do (pure (_get_HFGITR_EL2_Type_nGCSEPP (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((IsFeatureImplemented FEAT_GCS) <&&> (do
                 (GetCurrentEXLOCKEN ())) <&&> (do
                 (pure (! (← (Halted ()))))))) && (__PSTATE_EXLOCK == 1#1)) : Bool)
          then (EXLOCKException ())
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_nGCSEPP == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (GCSPOPCX ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((IsFeatureImplemented FEAT_GCS) <&&> (do
                     (GetCurrentEXLOCKEN ())) <&&> (do
                     (pure (! (← (Halted ()))))))) && (__PSTATE_EXLOCK == 1#1)) : Bool)
              then (EXLOCKException ())
              else (GCSPOPCX ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((IsFeatureImplemented FEAT_GCS) <&&> (do
                         (GetCurrentEXLOCKEN ())) <&&> (do
                         (pure (! (← (Halted ()))))))) && (__PSTATE_EXLOCK == 1#1)) : Bool)
                  then (EXLOCKException ())
                  else (GCSPOPCX ()))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPOPX_SysOpsWrite_f5624b6324bc7c49 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (GCSPOPX ())
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (GCSPOPX ())
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (GCSPOPX ())
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPUSHM_SysOpsWrite_7d31b427953fb1be (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __GCSCRE0_EL1_PUSHMEn ← (( do (pure (_get_GCSCRE0_EL1_Type_PUSHMEn (← readReg GCSCRE0_EL1))) ) : SailM (BitVec 1) )
  let __GCSCR_EL1_PUSHMEn ← (( do (pure (_get_GCSCR_EL1_Type_PUSHMEn (← readReg GCSCR_EL1))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_nGCSPUSHM_EL1 ← (( do (pure (_get_HFGITR_EL2_Type_nGCSPUSHM_EL1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __GCSCR_EL2_PUSHMEn ← (( do (pure (_get_GCSCR_EL2_Type_PUSHMEn (← readReg GCSCR_EL2))) ) : SailM (BitVec 1) )
  let __GCSCR_EL3_PUSHMEn ← (( do (pure (_get_GCSCR_EL3_Type_PUSHMEn (← readReg GCSCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((((! (← (EL2Enabled ()))) || (__HCR_EL2_TGE != 1#1)) && (__GCSCRE0_EL1_PUSHMEn == 0#1)) : Bool)
      then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
      else
        (do
          if ((((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) && (__GCSCRE0_EL1_PUSHMEn == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (GCSPUSHM (← (X_read t 64)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((__GCSCR_EL1_PUSHMEn == 0#1) : Bool)
          then (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_nGCSPUSHM_EL1 == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (GCSPUSHM (← (X_read t 64)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__GCSCR_EL2_PUSHMEn == 0#1) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (GCSPUSHM (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__GCSCR_EL3_PUSHMEn == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (GCSPUSHM (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSPUSHX_SysOpsWrite_c023a281d843c45a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_EXLOCK ← (( do (pure (← readReg PSTATE).EXLOCK) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_nGCSEPP ← (( do (pure (_get_HFGITR_EL2_Type_nGCSEPP (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((IsFeatureImplemented FEAT_GCS) <&&> (do
                 (GetCurrentEXLOCKEN ())) <&&> (do
                 (pure (! (← (Halted ()))))))) && (__PSTATE_EXLOCK == 0#1)) : Bool)
          then (EXLOCKException ())
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_nGCSEPP == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (GCSPUSHX ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((IsFeatureImplemented FEAT_GCS) <&&> (do
                     (GetCurrentEXLOCKEN ())) <&&> (do
                     (pure (! (← (Halted ()))))))) && (__PSTATE_EXLOCK == 0#1)) : Bool)
              then (EXLOCKException ())
              else (GCSPUSHX ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((IsFeatureImplemented FEAT_GCS) <&&> (do
                         (GetCurrentEXLOCKEN ())) <&&> (do
                         (pure (! (← (Halted ()))))))) && (__PSTATE_EXLOCK == 0#1)) : Bool)
                  then (EXLOCKException ())
                  else (GCSPUSHX ()))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def GCSSS1_SysOpsWrite_5eb47650d9a586f4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (GCSSS1 (← (X_read t 64)))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (GCSSS1 (← (X_read t 64)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (GCSSS1 (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (GCSSS1 (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def IC_IALLUIS_SysOpsWrite_3eb8cc845c2f9444 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TPU ← (( do (pure (_get_HCR_EL2_Type_TPU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TICAB ← (( do (pure (_get_HCR_EL2_Type_TICAB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_ICIALLUIS ← (( do (pure (_get_HFGITR_EL2_Type_ICIALLUIS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPU == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TICAB == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_ICIALLUIS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_IC CacheOpScope_ALLUIS))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_IC CacheOpScope_ALLUIS)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_IC CacheOpScope_ALLUIS)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def IC_IALLU_SysOpsWrite_11cf556c15dd6d58 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TPU ← (( do (pure (_get_HCR_EL2_Type_TPU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TOCU ← (( do (pure (_get_HCR_EL2_Type_TOCU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_ICIALLU ← (( do (pure (_get_HFGITR_EL2_Type_ICIALLU (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FB ← (( do (pure (_get_HCR_EL2_Type_FB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPU == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TOCU == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_ICIALLU == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_IC CacheOpScope_ALLUIS)
                      else (AArch64_IC CacheOpScope_ALLU)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_IC CacheOpScope_ALLU)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_IC CacheOpScope_ALLU)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def IC_IVAU_SysOpsWrite_f40d5c6453a840a5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCI ← (( do (pure (_get_SCTLR_EL1_Type_UCI (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPU ← (( do (pure (_get_HCR_EL2_Type_TPU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TOCU ← (( do (pure (_get_HCR_EL2_Type_TOCU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_ICIVAU ← (( do (pure (_get_HFGITR_EL2_Type_ICIVAU (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCI ← (( do (pure (_get_SCTLR_EL2_Type_UCI (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCI == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TPU == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TOCU == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_ICIVAU == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCI == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_IC__1 (← (X_read t 64)) CacheOpScope_PoU))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TPU == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TOCU == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_ICIVAU == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (AArch64_IC__1 (← (X_read t 64)) CacheOpScope_PoU))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_IC__1 (← (X_read t 64)) CacheOpScope_PoU)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_IC__1 (← (X_read t 64)) CacheOpScope_PoU)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE1IS_SysOpsWrite_03d7588893774850 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_ISH TLBI_ExcludeXS)
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_ISH TLBI_ExcludeXS)
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE1IS_SysOpsWrite_549e403ce92161b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_ISH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_ISH TLBI_AllAttr)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE1OS_SysOpsWrite_614f5311238ca5e2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_OSH TLBI_ExcludeXS)
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_OSH TLBI_ExcludeXS)
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE1OS_SysOpsWrite_a4cd3a06ce23d819 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_OSH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_OSH TLBI_AllAttr)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE1_SysOpsWrite_23dd50d9423d8d4d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_NSH TLBI_ExcludeXS)
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_NSH TLBI_ExcludeXS)
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE1_SysOpsWrite_b217b426d8c641ae (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_NSH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_NSH TLBI_AllAttr)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE2IS_SysOpsWrite_710719471e64d3ba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_ISH TLBI_AllAttr)
              else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_ISH TLBI_AllAttr))
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
                      then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_ISH TLBI_AllAttr)
                      else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_ISH TLBI_AllAttr)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE2IS_SysOpsWrite_8a96112ff6953240 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_ISH TLBI_ExcludeXS)
                  else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_ISH TLBI_ExcludeXS))
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
                          then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_ISH TLBI_ExcludeXS)
                          else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_ISH TLBI_ExcludeXS)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE2OS_SysOpsWrite_1134fdc29a86072a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_OSH TLBI_ExcludeXS)
                  else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_OSH TLBI_ExcludeXS))
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
                          then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_OSH TLBI_ExcludeXS)
                          else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_OSH TLBI_ExcludeXS)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE2OS_SysOpsWrite_b46584bc29297df9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_OSH TLBI_AllAttr)
              else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_OSH TLBI_AllAttr))
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
                      then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_OSH TLBI_AllAttr)
                      else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_OSH TLBI_AllAttr)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE2_SysOpsWrite_6a07d2a37a89d31f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_NSH TLBI_ExcludeXS)
                  else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_NSH TLBI_ExcludeXS))
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
                          then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_NSH TLBI_ExcludeXS)
                          else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_NSH TLBI_ExcludeXS)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE2_SysOpsWrite_e9f6ac4ef52598b3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_NSH TLBI_AllAttr)
              else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_NSH TLBI_AllAttr))
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
                      then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL20 Shareability_NSH TLBI_AllAttr)
                      else (AArch64_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_NSH TLBI_AllAttr)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE3IS_SysOpsWrite_95e13b1ef487429e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL3)) Regime_EL3 Shareability_ISH TLBI_ExcludeXS)
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE3IS_SysOpsWrite_f68dcd86f3998afd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL3)) Regime_EL3 Shareability_ISH TLBI_AllAttr)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE3OS_SysOpsWrite_7d60d9e9832a86fc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL3)) Regime_EL3 Shareability_OSH TLBI_AllAttr)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE3OS_SysOpsWrite_f5180bd2c6904111 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL3)) Regime_EL3 Shareability_OSH TLBI_ExcludeXS)
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE3_SysOpsWrite_154b769b60a9a83a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL3)) Regime_EL3 Shareability_NSH TLBI_ExcludeXS)
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ALLE3_SysOpsWrite_f67a5db4b11c6ca5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_ALL (← (SecurityStateAtEL EL3)) Regime_EL3 Shareability_NSH TLBI_AllAttr)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ASIDE1IS_SysOpsWrite_15d557e1f93ce504 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIASIDE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIASIDE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIASIDE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ASIDE1IS_SysOpsWrite_3a685bcc71f41a1f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIASIDE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIASIDE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIASIDE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ASIDE1OS_SysOpsWrite_5c902fb0e3a0ba5e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIASIDE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIASIDE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIASIDE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_ASIDE1OS_SysOpsWrite_c650faaab3ae9387 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIASIDE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIASIDE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIASIDE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ASIDE1_SysOpsWrite_06d13305aa0971fa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIASIDE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIASIDE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIASIDE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr (← (X_read t 64))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_ASIDE1_SysOpsWrite_43318f45323f6d95 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIASIDE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIASIDE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIASIDE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_ASID (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1IS_SysOpsWrite_4c58dae59e564c5f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1IS_SysOpsWrite_ccc65f430a044914 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1OS_SysOpsWrite_309d90a600b530a7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1OS_SysOpsWrite_39b2c10069047b39 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1_SysOpsWrite_97895c8e9b4d80f7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1_SysOpsWrite_b3136916ac77cb10 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2LE1IS_SysOpsWrite_48fbca66415d71e4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2LE1IS_SysOpsWrite_9d56cb10a3da298e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2LE1OS_SysOpsWrite_41165e80f36dc5fa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2LE1OS_SysOpsWrite_f065e8faf0d6b28c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2LE1_SysOpsWrite_78a7997e8d77efab (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_IPAS2LE1_SysOpsWrite_cf8d18b6c0e5014a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_PAALLOS_SysOpsWrite_b02935bd045e4472 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_PAALL Shareability_OSH)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_PAALL_SysOpsWrite_30c81768c02bd90b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_PAALL Shareability_NSH)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2E1IS_SysOpsWrite_7f8b016dbe13814c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2E1IS_SysOpsWrite_f517d8205e0bc7df (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2E1OS_SysOpsWrite_2c91dee891ab3686 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2E1OS_SysOpsWrite_ed6e64c76758f7a2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2E1_SysOpsWrite_1f3af7628a95cec3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2E1_SysOpsWrite_49a01b03635148d3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1IS_SysOpsWrite_34cdbedbc256d566 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1IS_SysOpsWrite_73eb52c0eda77b8c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1OS_SysOpsWrite_54085ab636364748 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1OS_SysOpsWrite_d4ca3cdc19ea21bb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1_SysOpsWrite_360bee3e5adad3b9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1_SysOpsWrite_643a317b5666a6f1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBI_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RPALOS_SysOpsWrite_a11d11817d32a6eb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RPA TLBILevel_Last (← (X_read t 64)) Shareability_OSH)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RPAOS_SysOpsWrite_a15697b49d6ed58f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RPA TLBILevel_Any (← (X_read t 64)) Shareability_OSH)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAAE1IS_SysOpsWrite_18faceee87b47845 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAAE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAAE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAAE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAAE1IS_SysOpsWrite_1ddd15964002c062 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAAE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAAE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAAE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAAE1OS_SysOpsWrite_b1f4b958ef6b7447 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAAE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAAE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAAE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAAE1OS_SysOpsWrite_c9ef60d478317354 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAAE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAAE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAAE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAAE1_SysOpsWrite_801459dbccf15998 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAAE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAAE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAAE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAAE1_SysOpsWrite_acd078309ca68103 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAAE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAAE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAAE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAALE1IS_SysOpsWrite_32a7dfc802182d9a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAALE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAALE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAALE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAALE1IS_SysOpsWrite_5a66384446cc9c01 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAALE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAALE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAALE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAALE1OS_SysOpsWrite_a50e7acf9414f0e5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAALE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAALE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAALE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAALE1OS_SysOpsWrite_e3ba04498a146810 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAALE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAALE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAALE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAALE1_SysOpsWrite_2add4c21d48f4ea4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAALE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAALE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAALE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAALE1_SysOpsWrite_57dbaa0ff0b8fdce (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAALE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAALE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAALE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE1IS_SysOpsWrite_2b703b96d2b79219 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE1IS_SysOpsWrite_2c882bcfeb863fe7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE1OS_SysOpsWrite_46e21ce75556305b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE1OS_SysOpsWrite_f77553e58265d00e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE1_SysOpsWrite_ab1d44d851006a7d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE1_SysOpsWrite_df0eae7799136807 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVAE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVAE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE2IS_SysOpsWrite_16afb405c0e2ea02 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE2IS_SysOpsWrite_f9126da69ce69c19 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE2OS_SysOpsWrite_0ebf53e3aa0f8f7f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE2OS_SysOpsWrite_46b110246aedd461 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE2_SysOpsWrite_ae783e9b4ab84ab2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE2_SysOpsWrite_b0982ca76d6c7651 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE3IS_SysOpsWrite_61186878beebdd00 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE3IS_SysOpsWrite_e7bda4e5b52e0dd2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE3OS_SysOpsWrite_51cc3eac56f81d7f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE3OS_SysOpsWrite_b68e938dbaed6553 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE3_SysOpsWrite_9115183869722fc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVAE3_SysOpsWrite_aa377993d94b4c2a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE1IS_SysOpsWrite_12cfd4d0d4a6c225 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVALE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVALE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVALE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE1IS_SysOpsWrite_9c213afe5c766789 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVALE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVALE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVALE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE1OS_SysOpsWrite_45c25f2a662eaa2a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVALE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVALE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVALE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE1OS_SysOpsWrite_4e52e85810812d01 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVALE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVALE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVALE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE1_SysOpsWrite_21535728b556e5b1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVALE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVALE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVALE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE1_SysOpsWrite_cc74fa175b762bc3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIRVALE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIRVALE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVALE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE2IS_SysOpsWrite_c832bf01bcbc2cc0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE2IS_SysOpsWrite_ca640565cc2dea92 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE2OS_SysOpsWrite_0b11b74e4b3a3cfe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE2OS_SysOpsWrite_36a17e51dcbb19d2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE2_SysOpsWrite_a051bc1bccde7cd9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE2_SysOpsWrite_be8d66432234a830 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE3IS_SysOpsWrite_7257c0dcb24e4a80 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE3IS_SysOpsWrite_879fb376d7b6807d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE3OS_SysOpsWrite_ac643f4910daad7d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE3OS_SysOpsWrite_bdb9e7fcdda16e82 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE3_SysOpsWrite_14a8b6cb081a1329 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_RVALE3_SysOpsWrite_c0f76daa7c4a5790 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAAE1IS_SysOpsWrite_b0e95e7b2139780d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAAE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAAE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAAE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAAE1IS_SysOpsWrite_c037245209e28a04 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAAE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAAE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAAE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAAE1OS_SysOpsWrite_c65f7d2b6a47a2f3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAAE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAAE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAAE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAAE1OS_SysOpsWrite_e3dbcbfec1559aff (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAAE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAAE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAAE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAAE1_SysOpsWrite_155f359039903b2f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAAE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAAE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAAE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAAE1_SysOpsWrite_2fa40a87479f02d6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAAE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAAE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAAE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAALE1IS_SysOpsWrite_210660f1a7d14921 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAALE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAALE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAALE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAALE1IS_SysOpsWrite_74cf3deb93f9c490 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAALE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAALE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAALE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAALE1OS_SysOpsWrite_0f5703d12bddab98 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAALE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAALE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAALE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAALE1OS_SysOpsWrite_29989c3f4da9352a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAALE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAALE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAALE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAALE1_SysOpsWrite_51c1b09ad1bac112 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAALE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAALE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAALE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAALE1_SysOpsWrite_a96cfc69a6f87bef (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAALE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAALE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAALE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE1IS_SysOpsWrite_4976b291164ac150 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE1IS_SysOpsWrite_c27f5fb50c845520 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAE1IS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAE1IS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE1OS_SysOpsWrite_7d3a74604ad2dbdf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE1OS_SysOpsWrite_8c67238bf7f814e9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBOS ← (( do (pure (_get_HCR_EL2_Type_TTLBOS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAE1OS ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAE1OS (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE1_SysOpsWrite_30eaded0ddf7ab9d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE1_SysOpsWrite_cdcaa8b8b8d87463 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FGTnXS ← (( do (pure (_get_HCRX_EL2_Type_FGTnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_TLBIVAE1 ← (( do (pure (_get_HFGITR_EL2_Type_TLBIVAE1 (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
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
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE2IS_SysOpsWrite_b944414311b6f47e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE2IS_SysOpsWrite_ba6a5005f8e50b0a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE2OS_SysOpsWrite_6f840e706adb25b2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE2OS_SysOpsWrite_f8b097ac65738708 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE2_SysOpsWrite_23241f5754371907 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE2_SysOpsWrite_ab883e6d7c8e2e48 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE3IS_SysOpsWrite_067b7469c1e1bb6d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE3IS_SysOpsWrite_26beb941bc870811 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE3OS_SysOpsWrite_1c55c5510bb06701 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE3OS_SysOpsWrite_b1a90c282b7de961 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE3_SysOpsWrite_41a4620adcceb248 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (X_read t 64)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VAE3_SysOpsWrite_de8987d56f578140 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (X_read t 64)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE1IS_SysOpsWrite_0978356bc7a2174b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVALE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE1IS_SysOpsWrite_9c420b123e788777 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVALE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE1OS_SysOpsWrite_98a393eb5d247245 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVALE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE1OS_SysOpsWrite_ea84e7b4286ea314 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVALE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE1_SysOpsWrite_21ea80b02f894ffa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT)) <&&> (do
                         (pure (! (HaveEL EL3))) <||> (do
                           (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVALE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE1_SysOpsWrite_a60433fa9400576b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVALE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE2IS_SysOpsWrite_854ef2fc0be4152d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE2IS_SysOpsWrite_b0e15fe998e26a14 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE2OS_SysOpsWrite_5e062a952a34f1d1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE2OS_SysOpsWrite_9fccdf3bc89cf2de (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE2_SysOpsWrite_2a4e0248c72159b4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                  else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64))))
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
                          then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))
                          else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def TLBI_VALE2_SysOpsWrite_2fb1c62ae3ec4f94 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
              else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64))))
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
                      then (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))
                      else (AArch64_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (X_read t 64)))))
              else (pure ()))))


