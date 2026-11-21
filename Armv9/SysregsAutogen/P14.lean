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
def PMEVTYPER_SysRegWrite32_51b82d68052aa3e2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (5 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 5 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (5 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 5 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 5 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 5 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_51fb35106f5676b7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (1 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 1 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (1 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 1 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 1 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 1 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_5328bc51c618fc92 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (3 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 3 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (3 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 3 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 3 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 3 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_59d93d7cd130a144 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (17 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 17 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (17 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 17 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 17 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 17 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_5cfcde71ee84f007 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (30 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 30 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (30 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 30 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 30 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 30 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_5d6bbab43fdc82f0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (22 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 22 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (22 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 22 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 22 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 22 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_5e6a7eed513b84e1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (25 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 25 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (25 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 25 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 25 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 25 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_6446dee6893e6f0c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (19 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 19 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (19 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 19 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 19 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 19 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_6b959d889d3d66da (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (24 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 24 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (24 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 24 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 24 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 24 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_73416eaea2ea531d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (14 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 14 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (14 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 14 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 14 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 14 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_7a2ddec1dbe177e8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (18 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 18 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (18 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 18 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 18 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 18 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_82b4f80451193782 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (2 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 2 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (2 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 2 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 2 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 2 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_863b5087474e4a64 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (11 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 11 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (11 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 11 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 11 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 11 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_8790f8c36b20943f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (7 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 7 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (7 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 7 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 7 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 7 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_944684756672e51b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (16 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 16 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (16 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 16 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 16 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 16 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_a8d64216580bbaf2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (28 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 28 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (28 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 28 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 28 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 28 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_d731b0e32007816c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (21 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 21 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (21 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 21 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 21 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 21 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_fc6d24db3b587aa8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (23 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                              then
                                (do
                                  if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                  then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                  else
                                    (do
                                      if ((← (ELUsingAArch32 EL1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else (PMEVTYPER_set 23 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (23 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                      then
                        (do
                          if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                          then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                          else
                            (do
                              if ((← (ELUsingAArch32 EL2)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else (PMEVTYPER_set 23 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMEVTYPER_set 23 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 23 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMINTENCLR_SysRegWrite32_3861e4c2893d3032 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TPM ← (( do (pure (_get_HDCR_Type_TPM (← (HDCR_read ())))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (PMINTENCLR_write (Mk_PMINTENCLR_Type (← (R_read t))))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMINTENCLR_write (Mk_PMINTENCLR_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMINTENCLR_write (Mk_PMINTENCLR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMINTENSET_SysRegWrite32_068b645854413351 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TPM ← (( do (pure (_get_HDCR_Type_TPM (← (HDCR_read ())))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (PMINTENSET_write (Mk_PMINTENSET_Type (← (R_read t))))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMINTENSET_write (Mk_PMINTENSET_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMINTENSET_write (Mk_PMINTENSET_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMOVSR_SysRegWrite32_afe1ff69a9fde1bd (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMOVS ← (( do (pure (_get_HDFGWTR_EL2_Type_PMOVS (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMOVS == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                      else (PMOVSR_write (Mk_PMOVSR_Type (← (R_read t)))))))))))))
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (PMOVSR_write (Mk_PMOVSR_Type (← (R_read t))))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMOVSR_write (Mk_PMOVSR_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMOVSR_write (Mk_PMOVSR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMOVSSET_SysRegWrite32_d042c47fdd8f3705 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMOVS ← (( do (pure (_get_HDFGWTR_EL2_Type_PMOVS (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMOVS == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                      else (PMOVSSET_write (Mk_PMOVSSET_Type (← (R_read t)))))))))))))
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (PMOVSSET_write (Mk_PMOVSSET_Type (← (R_read t))))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMOVSSET_write (Mk_PMOVSSET_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMOVSSET_write (Mk_PMOVSSET_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSELR_SysRegWrite32_3f6f0842c8047d3f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMSELR_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMSELR_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                 (pure (((_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0)) +++ ((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)))) == 0b000#3))) <||> (do
                 (pure (! (← (IsFeatureImplemented FEAT_PMUv3p9)))) <&&> (do
                   (pure (((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) == 0b00#2))))))) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if ((←((ELUsingAArch32 EL1) <&&> (do
                   (pure (((_get_PMUSERENR_Type_ER (← (PMUSERENR_read ()))) +++ (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) == 0b00#2))))) : Bool)
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
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMSELR_EL0 == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                      else (PMSELR_write (Mk_PMSELR_Type (← (R_read t)))))))))))))
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (PMSELR_write (Mk_PMSELR_Type (← (R_read t))))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMSELR_write (Mk_PMSELR_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMSELR_write (Mk_PMSELR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSWINC_SysRegWrite32_9b4c9b84c8e7597b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMSWINC_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMSWINC_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                 (pure (((_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0)) +++ ((_get_PMUSERENR_EL0_Type_SW (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)))) == 0b000#3))) <||> (do
                 (pure (! (← (IsFeatureImplemented FEAT_PMUv3p9)))) <&&> (do
                   (pure (((_get_PMUSERENR_EL0_Type_SW (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) == 0b00#2))))))) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
          else
            (do
              if ((←((ELUsingAArch32 EL1) <&&> (do
                   (pure (((_get_PMUSERENR_Type_SW (← (PMUSERENR_read ()))) +++ (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) == 0b00#2))))) : Bool)
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
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMSWINC_EL0 == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                      else (PMSWINC_write (Mk_PMSWINC_Type (← (R_read t)))))))))))))
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (PMSWINC_write (Mk_PMSWINC_Type (← (R_read t))))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMSWINC_write (Mk_PMSWINC_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMSWINC_write (Mk_PMSWINC_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMUSERENR_SysRegWrite32_5b91165bfc334c29 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TPM ← (( do (pure (_get_HDCR_Type_TPM (← (HDCR_read ())))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                              else (PMUSERENR_write (Mk_PMUSERENR_Type (← (R_read t))))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (PMUSERENR_write (Mk_PMUSERENR_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMUSERENR_write (Mk_PMUSERENR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMXEVCNTR_SysRegWrite32_4f0aa881614b1f11 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TPM ← (( do (pure (_get_HDCR_Type_TPM (← (HDCR_read ())))) ) : SailM (BitVec 1) )
  if (((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) ≥b 31) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVCNTRn_EL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if ((←((EL2Enabled ()) <&&> (do
                                               (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                                          then
                                            (do
                                              if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                              then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                              else
                                                (do
                                                  if ((← (ELUsingAArch32 EL1)) : Bool)
                                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                                  else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                              else (__set_selected_PMEVCNTR (← (R_read t)))))))))))))
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                                  then
                                    (do
                                      if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                      then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                      else
                                        (do
                                          if ((← (ELUsingAArch32 EL2)) : Bool)
                                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                          else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                      else (__set_selected_PMEVCNTR (← (R_read t))))))))))
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (__set_selected_PMEVCNTR (← (R_read t)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (__set_selected_PMEVCNTR (← (R_read t)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def PMXEVTYPER_SysRegWrite32_853b58a36392d331 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TPM ← (( do (pure (_get_HDCR_Type_TPM (← (HDCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) != 31)) <&&> (do
       (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) ≥b 31))))) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__PMUSERENR_EN == 0#1)) : Bool)
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
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T9 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if ((((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if ((←((EL2Enabled ()) <&&> (do
                                               (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) != 31))) <&&> (do
                                               (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                                          then
                                            (do
                                              if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                              then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                              else
                                                (do
                                                  if ((← (ELUsingAArch32 EL1)) : Bool)
                                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                                  else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                              else
                                                (do
                                                  if (((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) == 31) : Bool)
                                                  then (PMCCFILTR_write (Mk_PMCCFILTR_Type (← (R_read t))))
                                                  else (__set_selected_PMEVTYPER (Mk_PMEVTYPER_Type (← (R_read t)))))))))))))))
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T9 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) != 31))) <&&> (do
                                       (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
                                  then
                                    (do
                                      if ((! (← (IsFeatureImplemented FEAT_FGT))) : Bool)
                                      then (pure (ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))
                                      else
                                        (do
                                          if ((← (ELUsingAArch32 EL2)) : Bool)
                                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                          else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          if (((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) == 31) : Bool)
                                          then (PMCCFILTR_write (Mk_PMCCFILTR_Type (← (R_read t))))
                                          else (__set_selected_PMEVTYPER (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) == 31) : Bool)
                          then (PMCCFILTR_write (Mk_PMCCFILTR_Type (← (R_read t))))
                          else (__set_selected_PMEVTYPER (Mk_PMEVTYPER_Type (← (R_read t)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) == 31) : Bool)
                      then (PMCCFILTR_write (Mk_PMCCFILTR_Type (← (R_read t))))
                      else (__set_selected_PMEVTYPER (Mk_PMEVTYPER_Type (← (R_read t)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def PRRR_SysRegWrite32_d60dcdae1cc2429d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T10 ← (( do (pure (_get_HSTR_EL2_Type_T10 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T10 ← (( do (pure (_get_HSTR_Type_T10 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then
                            (do
                              if ((← (EAEisOne ())) : Bool)
                              then (MAIR0_NS_write (Mk_MAIR0_Type (← (R_read t))))
                              else (PRRR_NS_write (Mk_PRRR_Type (← (R_read t)))))
                          else
                            (do
                              if ((← (EAEisOne ())) : Bool)
                              then (MAIR0_write (Mk_MAIR0_Type (← (R_read t))))
                              else (PRRR_write (Mk_PRRR_Type (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then
                (do
                  if ((← (EAEisOne ())) : Bool)
                  then (MAIR0_NS_write (Mk_MAIR0_Type (← (R_read t))))
                  else (PRRR_NS_write (Mk_PRRR_Type (← (R_read t)))))
              else
                (do
                  if ((← (EAEisOne ())) : Bool)
                  then (MAIR0_write (Mk_MAIR0_Type (← (R_read t))))
                  else (PRRR_write (Mk_PRRR_Type (← (R_read t))))))
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
                      if ((←((pure (__SCR_NS == 0#1)) <&&> (do
                           (pure (BEq.beq (← readReg CP15SDISABLE2) Signal_High))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((← (EAEisOne ())) : Bool)
                          then
                            (do
                              if ((__SCR_NS == 0#1) : Bool)
                              then (MAIR0_S_write (Mk_MAIR0_Type (← (R_read t))))
                              else (MAIR0_NS_write (Mk_MAIR0_Type (← (R_read t)))))
                          else
                            (do
                              if ((__SCR_NS == 0#1) : Bool)
                              then writeReg PRRR_S (Mk_PRRR_Type (← (R_read t)))
                              else (PRRR_NS_write (Mk_PRRR_Type (← (R_read t))))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def RMR_SysRegWrite32_9dfdd4710efdf52a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((IsHighestEL EL1) : Bool)
          then (RMR_write (Mk_RMR_Type (← (R_read t))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((BEq.beq (← readReg CP15SDISABLE) Signal_High) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((BEq.beq (← readReg CP15SDISABLE2) Signal_High) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (RMR_write (Mk_RMR_Type (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCR_SysRegWrite32_4891195fead51a46 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
                  if ((←((pure (! (← (ELUsingAArch32 EL2)))) <&&> (do
                       (pure (((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) == 0b01#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((! (← (ELUsingAArch32 EL3))) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg SCR (Mk_SCR_Type (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR_SysRegWrite32_88c9496795c226a4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (__set_SCTLR_NS (Mk_SCTLR_Type (← (R_read t))))
                          else (__set_SCTLR (Mk_SCTLR_Type (← (R_read t)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (__set_SCTLR_NS (Mk_SCTLR_Type (← (R_read t))))
              else (__set_SCTLR (Mk_SCTLR_Type (← (R_read t)))))
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
                      if ((←((pure (__SCR_NS == 0#1)) <&&> (do
                           (pure (BEq.beq (← readReg CP15SDISABLE2) Signal_High))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((__SCR_NS == 0#1) : Bool)
                          then (__set_SCTLR_S (Mk_SCTLR_Type (← (R_read t))))
                          else (__set_SCTLR_NS (Mk_SCTLR_Type (← (R_read t)))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SDCR_SysRegWrite32_4a9ed44cdafd01dd (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
                  if ((←((pure (! (← (ELUsingAArch32 EL2)))) <&&> (do
                       (pure (((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) +++ (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) == 0b01#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((! (← (ELUsingAArch32 EL3))) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((BEq.beq (← readReg CP15SDISABLE2) Signal_High) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg SDCR (Mk_SDCR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SDER_SysRegWrite32_78d36c9dd1d8d07c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
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
                  if ((! (← (IsCurrentSecurityState SS_Secure))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))
                          else (SDER_write (Mk_SDER_Type (← (R_read t)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((BEq.beq (← readReg CP15SDISABLE2) Signal_High) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (SDER_write (Mk_SDER_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIALLHIS_SysRegWrite32_3f104fb53eee9e89 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_ISH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch32_TLBI_ALL SS_NonSecure Regime_EL2 Shareability_ISH TLBI_AllAttr))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIALLH_SysRegWrite32_ce3aa1e39dfad34d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_ALL (← (SecurityStateAtEL EL2)) Regime_EL2 Shareability_NSH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch32_TLBI_ALL SS_NonSecure Regime_EL2 Shareability_NSH TLBI_AllAttr))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIALLIS_SysRegWrite32_26b5c3b29f92f5ea (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TTLBIS ← (( do (pure (_get_HCR2_Type_TTLBIS (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TTLBIS == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS)
                                  else (AArch32_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_ALL (← (SecurityStateAtEL EL3)) Regime_EL30 Shareability_ISH TLBI_ExcludeXS)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIALLNSNHIS_SysRegWrite32_934a7e1a0cc96b4a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_ISH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch32_TLBI_ALL SS_NonSecure Regime_EL10 Shareability_ISH TLBI_AllAttr))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIALLNSNH_SysRegWrite32_31faa2646b198591 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_NSH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch32_TLBI_ALL SS_NonSecure Regime_EL10 Shareability_NSH TLBI_AllAttr))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIALL_SysRegWrite32_b21af7f2b4a8cf08 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FB ← (( do (pure (_get_HCR_EL2_Type_FB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FB ← (( do (pure (_get_HCR_Type_FB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FB == 1#1)) : Bool)
                          then
                            (do
                              if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                     (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                     (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                              then (AArch32_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS)
                              else (AArch32_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR_FB == 1#1)) : Bool)
                              then (AArch32_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr)
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS)
                                  else (AArch32_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VMALL (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_ALL (← (SecurityStateAtEL EL3)) Regime_EL30 Shareability_NSH TLBI_ExcludeXS)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIASIDIS_SysRegWrite32_03d2fed54ae109c3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TTLBIS ← (( do (pure (_get_HCR2_Type_TTLBIS (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TTLBIS == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS (← (R_read t)))
                                  else (AArch32_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_ASID (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_ISH TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIASID_SysRegWrite32_fb38392a6a11d341 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FB ← (( do (pure (_get_HCR_EL2_Type_FB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FB ← (( do (pure (_get_HCR_Type_FB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FB == 1#1)) : Bool)
                          then
                            (do
                              if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                     (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                     (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                              then (AArch32_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_ExcludeXS (← (R_read t)))
                              else (AArch32_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr (← (R_read t))))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR_FB == 1#1)) : Bool)
                              then (AArch32_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBI_AllAttr (← (R_read t)))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS (← (R_read t)))
                                  else (AArch32_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_ASID (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_NSH TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIIPAS2IS_SysRegWrite32_e4867c386886a0ac (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (pure ())
                      else (AArch32_TLBI_IPAS2 SS_NonSecure Regime_EL10 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIIPAS2LIS_SysRegWrite32_4ae44938f6bf59ab (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (pure ())
                      else (AArch32_TLBI_IPAS2 SS_NonSecure Regime_EL10 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIIPAS2L_SysRegWrite32_a0e257684d03ee99 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (pure ())
                      else (AArch32_TLBI_IPAS2 SS_NonSecure Regime_EL10 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIIPAS2_SysRegWrite32_0f58707a5d9a37dd (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (pure ())
                      else (AArch32_TLBI_IPAS2 SS_NonSecure Regime_EL10 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVAAIS_SysRegWrite32_96d1aeda66ab1386 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TTLBIS ← (( do (pure (_get_HCR2_Type_TTLBIS (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TTLBIS == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (R_read t)))
                                  else (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVAALIS_SysRegWrite32_213090c663fe2ea7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TTLBIS ← (( do (pure (_get_HCR2_Type_TTLBIS (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TTLBIS == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (R_read t)))
                                  else (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVAAL_SysRegWrite32_b622dab84122dbc0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FB ← (( do (pure (_get_HCR_EL2_Type_FB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FB ← (( do (pure (_get_HCR_Type_FB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FB == 1#1)) : Bool)
                          then
                            (do
                              if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                     (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                     (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                              then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (R_read t)))
                              else (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t))))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR_FB == 1#1)) : Bool)
                              then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (R_read t)))
                                  else (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVAA_SysRegWrite32_cb49c2a9a16e5968 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FB ← (( do (pure (_get_HCR_EL2_Type_FB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FB ← (( do (pure (_get_HCR_Type_FB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FB == 1#1)) : Bool)
                          then
                            (do
                              if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                     (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                     (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                              then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (R_read t)))
                              else (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t))))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR_FB == 1#1)) : Bool)
                              then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (R_read t)))
                                  else (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_VAA (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVAHIS_SysRegWrite32_5da1d1a785b555e8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch32_TLBI_VA SS_NonSecure Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVAH_SysRegWrite32_4fb355f41064966b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch32_TLBI_VA SS_NonSecure Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVAIS_SysRegWrite32_bfc80b2d7757a07f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TTLBIS ← (( do (pure (_get_HCR2_Type_TTLBIS (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TTLBIS == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (R_read t)))
                                  else (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVALHIS_SysRegWrite32_89a451ea9208e882 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch32_TLBI_VA SS_NonSecure Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVALH_SysRegWrite32_e910bf47238cb4c5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (AArch32_TLBI_VA SS_NonSecure Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVALIS_SysRegWrite32_ff59541f99afcbcf (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLBIS ← (( do (pure (_get_HCR_EL2_Type_TTLBIS (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TTLBIS ← (( do (pure (_get_HCR2_Type_TTLBIS (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TTLBIS == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (R_read t)))
                                  else (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVAL_SysRegWrite32_db84fa64000a2011 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FB ← (( do (pure (_get_HCR_EL2_Type_FB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FB ← (( do (pure (_get_HCR_Type_FB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FB == 1#1)) : Bool)
                          then
                            (do
                              if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                     (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                     (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                              then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS (← (R_read t)))
                              else (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t))))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR_FB == 1#1)) : Bool)
                              then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS (← (R_read t)))
                                  else (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBIMVA_SysRegWrite32_f66a0ca0f4cc9ff0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FB ← (( do (pure (_get_HCR_EL2_Type_FB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_FnXS ← (( do (pure (_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FB ← (( do (pure (_get_HCR_Type_FB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T8 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T8 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TTLB == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FB == 1#1)) : Bool)
                          then
                            (do
                              if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                     (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                     (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                              then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS (← (R_read t)))
                              else (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t))))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR_FB == 1#1)) : Bool)
                              then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
                              else
                                (do
                                  if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                         (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                                  then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (R_read t)))
                                  else (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_TLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_TLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDRPRW_SysRegWrite32_5caaac18c68f924b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (ELUsingAArch32 EL3)))) : Bool)
                  then (TPIDRPRW_NS_write (← (R_read t)))
                  else (TPIDRPRW_write (← (R_read t))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (TPIDRPRW_NS_write (← (R_read t)))
              else (TPIDRPRW_write (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg TPIDRPRW_S (← (R_read t))
                  else (TPIDRPRW_NS_write (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDRURO_SysRegWrite32_2b144f3027758b96 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (ELUsingAArch32 EL3)))) : Bool)
                  then (TPIDRURO_NS_write (← (R_read t)))
                  else (TPIDRURO_write (← (R_read t))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (TPIDRURO_NS_write (← (R_read t)))
              else (TPIDRURO_write (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg TPIDRURO_S (← (R_read t))
                  else (TPIDRURO_NS_write (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDRURW_SysRegWrite32_cb192fad8255358c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_TPIDR_EL0 ← (( do (pure (_get_HFGWTR_EL2_Type_TPIDR_EL0 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
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
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TPIDR_EL0 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (TPIDRURW_write (← (R_read t))))))
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
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (ELUsingAArch32 EL3)))) : Bool)
                  then (TPIDRURW_NS_write (← (R_read t)))
                  else (TPIDRURW_write (← (R_read t))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (TPIDRURW_NS_write (← (R_read t)))
              else (TPIDRURW_write (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg TPIDRURW_S (← (R_read t))
                  else (TPIDRURW_NS_write (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TRFCR_SysRegWrite32_e7012a38712cc44a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TTRF ← (( do (pure (_get_MDCR_EL3_Type_TTRF (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SDCR_TTRF ← (( do (pure (_get_SDCR_Type_TTRF (← readReg SDCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TTRF ← (( do (pure (_get_MDCR_EL2_Type_TTRF (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TTRF ← (( do (pure (_get_HDCR_Type_TTRF (← (HDCR_read ())))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SDCR_TTRF == 1#1)) : Bool)
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TTRF == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HDCR_TTRF == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SDCR_TTRF == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (TRFCR_write (Mk_TRFCR_Type (← (R_read t))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SDCR_TTRF == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SDCR_TTRF == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (TRFCR_write (Mk_TRFCR_Type (← (R_read t))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SDCR_TTRF == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (TRFCR_write (Mk_TRFCR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBCR2_SysRegWrite32_06c6fc8db37664f3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T2 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (TTBCR2_NS_write (Mk_TTBCR2_Type (← (R_read t))))
                          else (TTBCR2_write (Mk_TTBCR2_Type (← (R_read t)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (TTBCR2_NS_write (Mk_TTBCR2_Type (← (R_read t))))
              else (TTBCR2_write (Mk_TTBCR2_Type (← (R_read t)))))
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
                      if ((←((pure (__SCR_NS == 0#1)) <&&> (do
                           (pure (BEq.beq (← readReg CP15SDISABLE2) Signal_High))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((__SCR_NS == 0#1) : Bool)
                          then writeReg TTBCR2_S (Mk_TTBCR2_Type (← (R_read t)))
                          else (TTBCR2_NS_write (Mk_TTBCR2_Type (← (R_read t)))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBCR_SysRegWrite32_4607ff14cabf6694 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T2 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (TTBCR_NS_write (Mk_TTBCR_Type (← (R_read t))))
                          else (TTBCR_write (Mk_TTBCR_Type (← (R_read t)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (TTBCR_NS_write (Mk_TTBCR_Type (← (R_read t))))
              else (TTBCR_write (Mk_TTBCR_Type (← (R_read t)))))
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
                      if ((←((pure (__SCR_NS == 0#1)) <&&> (do
                           (pure (BEq.beq (← readReg CP15SDISABLE2) Signal_High))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((__SCR_NS == 0#1) : Bool)
                          then writeReg TTBCR_S (Mk_TTBCR_Type (← (R_read t)))
                          else (TTBCR_NS_write (Mk_TTBCR_Type (← (R_read t)))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR0_SysRegWrite32_455c3a8e0a51a871 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T2 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then writeReg TTBR0_NS (Sail.BitVec.updateSubrange (← readReg TTBR0_NS) 31 0 (← (R_read t)))
                          else (TTBR0_write (Mk_TTBR0_Type (Sail.BitVec.updateSubrange (← (TTBR0_read ())) 31 0 (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then writeReg TTBR0_NS (Sail.BitVec.updateSubrange (← readReg TTBR0_NS) 31 0 (← (R_read t)))
              else (TTBR0_write (Mk_TTBR0_Type (Sail.BitVec.updateSubrange (← (TTBR0_read ())) 31 0 (← (R_read t))))))
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
                      then writeReg TTBR0_S (Sail.BitVec.updateSubrange (← readReg TTBR0_S) 31 0 (← (R_read t)))
                      else writeReg TTBR0_NS (Sail.BitVec.updateSubrange (← readReg TTBR0_NS) 31 0 (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR1_SysRegWrite32_388bd96b6dea14cc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T2 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then writeReg TTBR1_NS (Sail.BitVec.updateSubrange (← readReg TTBR1_NS) 31 0 (← (R_read t)))
                          else (TTBR1_write (Mk_TTBR1_Type (Sail.BitVec.updateSubrange (← (TTBR1_read ())) 31 0 (← (R_read t))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then writeReg TTBR1_NS (Sail.BitVec.updateSubrange (← readReg TTBR1_NS) 31 0 (← (R_read t)))
              else (TTBR1_write (Mk_TTBR1_Type (Sail.BitVec.updateSubrange (← (TTBR1_read ())) 31 0 (← (R_read t))))))
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
                      then writeReg TTBR1_S (Sail.BitVec.updateSubrange (← readReg TTBR1_S) 31 0 (← (R_read t)))
                      else writeReg TTBR1_NS (Sail.BitVec.updateSubrange (← readReg TTBR1_NS) 31 0 (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VBAR_SysRegWrite32_bc2b5cd33d4ee53c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
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
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (ELUsingAArch32 EL3)))) : Bool)
                  then (VBAR_NS_write (← (R_read t)))
                  else (VBAR_write (← (R_read t))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (VBAR_NS_write (← (R_read t)))
              else (VBAR_write (← (R_read t))))
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
                      if ((←((pure (__SCR_NS == 0#1)) <&&> (do
                           (pure (BEq.beq (← readReg CP15SDISABLE2) Signal_High))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((__SCR_NS == 0#1) : Bool)
                          then writeReg VBAR_S (← (R_read t))
                          else (VBAR_NS_write (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VDFSR_SysRegWrite32_a0962e93b6e4f29f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (VDFSR_write (Mk_VDFSR_Type (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (VDFSR_write (Mk_VDFSR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VDISR_SysRegWrite32_d6e68a15b17084cf (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T12 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T12 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (VDISR_write (Mk_VDISR_Type (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (VDISR_write (Mk_VDISR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VMPIDR_SysRegWrite32_954adcfdf7aeec04 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (VMPIDR_write (Mk_VMPIDR_Type (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (pure ())
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (VMPIDR_write (Mk_VMPIDR_Type (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VPIDR_SysRegWrite32_deaaa2df067d2d32 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (VPIDR_write (Mk_VPIDR_Type (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (pure ())
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (VPIDR_write (Mk_VPIDR_Type (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VTCR_SysRegWrite32_481811658d5f359e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T2 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (VTCR_write (Mk_VTCR_Type (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (VTCR_write (Mk_VTCR_Type (← (R_read t)))))
              else (pure ()))))

def DBGDTRRXint_STC_521dc9133ebece9c (coproc : (BitVec 4)) (CRd : (BitVec 4)) (address : (BitVec 32)) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __DBGDSCRext_UDCCdis ← (( do (pure (_get_DBGDSCRext_Type_UDCCdis (← (DBGDSCRext_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TDCC ← (( do (pure (_get_HDCR_Type_TDCC (← (HDCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SDCR_TDCC ← (( do (pure (_get_SDCR_Type_TDCC (← readReg SDCR))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  if ((← (Halted ())) : Bool)
  then (MemA_set address 4 (← (DBGDTRRXint_read ())))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__MDSCR_EL1_TDCC == 1#1)) : Bool)
          then
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                   (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x06#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__DBGDSCRext_UDCCdis == 1#1)) : Bool)
              then
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do
                                 (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2)))))) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)) <&&> (do
                                   (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1)) <||> (do
                                     (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2)))))) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                      then (AArch32_TakeMonitorTrapException ())
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                          then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                                          else (MemA_set address 4 (← (DBGDTRRXint_read ()))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)) <&&> (do
                               (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                  then (AArch32_TakeMonitorTrapException ())
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                                      else (MemA_set address 4 (← (DBGDTRRXint_read ()))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeMonitorTrapException ())
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                          else (MemA_set address 4 (← (DBGDTRRXint_read ()))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((__PSTATE_M != M32_Monitor) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeMonitorTrapException ())
                      else (MemA_set address 4 (← (DBGDTRRXint_read ()))))
                  else (pure ())))))

def DBGDTRTXint_LDC_da4baa792b999a1f (coproc : (BitVec 4)) (CRd : (BitVec 4)) (address : (BitVec 32)) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __DBGDSCRext_UDCCdis ← (( do (pure (_get_DBGDSCRext_Type_UDCCdis (← (DBGDSCRext_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TDCC ← (( do (pure (_get_HDCR_Type_TDCC (← (HDCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SDCR_TDCC ← (( do (pure (_get_SDCR_Type_TDCC (← readReg SDCR))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  if ((← (Halted ())) : Bool)
  then (DBGDTRTXint_write (Mk_DBGDTRTXint_Type (← (MemA_read address 4))))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((! (← (ELUsingAArch32 EL1))) && (__MDSCR_EL1_TDCC == 1#1)) : Bool)
          then
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                   (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x06#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__DBGDSCRext_UDCCdis == 1#1)) : Bool)
              then
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                      else (sailThrow ((Error_Undefined ())) : SailM Unit)))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do
                                 (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2)))))) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)) <&&> (do
                                   (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1)) <||> (do
                                     (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2)))))) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                      then (AArch32_TakeMonitorTrapException ())
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                          then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                                          else (DBGDTRTXint_write (Mk_DBGDTRTXint_Type (← (MemA_read address 4)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)) <&&> (do
                               (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                  then (AArch32_TakeMonitorTrapException ())
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                                      else (DBGDTRTXint_write (Mk_DBGDTRTXint_Type (← (MemA_read address 4)))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeMonitorTrapException ())
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8))
                          else (DBGDTRTXint_write (Mk_DBGDTRTXint_Type (← (MemA_read address 4)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((__PSTATE_M != M32_Monitor) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeMonitorTrapException ())
                      else (DBGDTRTXint_write (Mk_DBGDTRTXint_Type (← (MemA_read address 4)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def PAR_EL1_SysRegRead128_8206ac7c9b0eef57 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_PAR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_PAR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_D128En ← (( do (pure (_get_HCRX_EL2_Type_D128En (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_PAR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_D128En == 0#1)))))) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (PAR_EL1_read ())) 127 64), (Sail.BitVec.extractLsb (← (PAR_EL1_read ())) 63 0)))
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (PAR_EL1_read ())) 127 64), (Sail.BitVec.extractLsb (← (PAR_EL1_read ())) 63 0)))
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (PAR_EL1_read ())) 127 64), (Sail.BitVec.extractLsb (← (PAR_EL1_read ())) 63 0)))
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def RCWMASK_EL1_SysRegRead128_7c7466f3a5148cfe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_RCWMASKEn ← (( do (pure (_get_SCR_EL3_Type_RCWMASKEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_nRCWMASK_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_nRCWMASK_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_D128En ← (( do (pure (_get_HCRX_EL2_Type_D128En (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_nRCWMASK_EL1 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_D128En == 0#1)))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg RCWMASK_EL1) 127 64), (Sail.BitVec.extractLsb (← readReg RCWMASK_EL1) 63 0)))
                                  (X_set (t +i 1) 64 __tup_0)
                                  (X_set t 64 __tup_1))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg RCWMASK_EL1) 127 64), (Sail.BitVec.extractLsb (← readReg RCWMASK_EL1) 63 0)))
                              (X_set (t +i 1) 64 __tup_0)
                              (X_set t 64 __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg RCWMASK_EL1) 127 64), (Sail.BitVec.extractLsb (← readReg RCWMASK_EL1) 63 0)))
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def RCWSMASK_EL1_SysRegRead128_7cac5e35b1fae5f9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_RCWMASKEn ← (( do (pure (_get_SCR_EL3_Type_RCWMASKEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR2_EL2_nRCWSMASK_EL1 ← (( do (pure (_get_HFGRTR2_EL2_Type_nRCWSMASK_EL1 (← readReg HFGRTR2_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_D128En ← (( do (pure (_get_HCRX_EL2_Type_D128En (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HFGRTR2_EL2_nRCWSMASK_EL1 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_D128En == 0#1)))))) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                              else
                                (do
                                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                                  then
                                    (do
                                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                                  else
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg RCWSMASK_EL1) 127 64), (Sail.BitVec.extractLsb (← readReg RCWSMASK_EL1) 63 0)))
                                      (X_set (t +i 1) 64 __tup_0)
                                      (X_set t 64 __tup_1)))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg RCWSMASK_EL1) 127 64), (Sail.BitVec.extractLsb (← readReg RCWSMASK_EL1) 63 0)))
                              (X_set (t +i 1) 64 __tup_0)
                              (X_set t 64 __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg RCWSMASK_EL1) 127 64), (Sail.BitVec.extractLsb (← readReg RCWSMASK_EL1) 63 0)))
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_ImpDefSysRegRead128 (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (t : Int) (t2 : Int) : SailM Unit := do
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL1_SysRegRead128_e74a87d5451e7769 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_TTBR0_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_TTBR0_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_D128En ← (( do (pure (_get_HCRX_EL2_Type_D128En (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TTBR0_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_D128En == 0#1)))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) ← do (Split (← (NVMem_read__1 (BitVec.toNat 0x200#12) 128)) 64)
                                  (X_set (t +i 1) 64 __tup_0)
                                  (X_set t 64 __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (Split (← (TTBR0_EL1_read ())) 64)
                                  (X_set (t +i 1) 64 __tup_0)
                                  (X_set t 64 __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let (__tup_0, __tup_1) ← do (Split (← (TTBR0_EL2_read ())) 64)
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))
                      else
                        (do
                          let (__tup_0, __tup_1) ← do (Split (← (TTBR0_EL1_read ())) 64)
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (Split (← (TTBR0_EL1_read ())) 64)
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL1_SysRegRead128_ef7a13f49fb9674d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
              let (__tup_0, __tup_1) ← do (Split (← (NVMem_read__1 (BitVec.toNat 0x200#12) 128)) 64)
              (X_set (t +i 1) 64 __tup_0)
              (X_set t 64 __tup_1))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let (__tup_0, __tup_1) ← do (Split (← (TTBR0_EL1_read ())) 64)
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))))
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
                      let (__tup_0, __tup_1) ← do (Split (← (TTBR0_EL1_read ())) 64)
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL2_SysRegRead128_05dc18b820cc86b7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (Split (← (TTBR0_EL2_read ())) 64)
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (Split (← (TTBR0_EL2_read ())) 64)
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL1_SysRegRead128_16388106e031d578 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
              let (__tup_0, __tup_1) ← do (Split (← (NVMem_read__1 (BitVec.toNat 0x210#12) 128)) 64)
              (X_set (t +i 1) 64 __tup_0)
              (X_set t 64 __tup_1))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let (__tup_0, __tup_1) ← do (Split (← (TTBR1_EL1_read ())) 64)
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))))
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
                      let (__tup_0, __tup_1) ← do (Split (← (TTBR1_EL1_read ())) 64)
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL2_SysRegRead128_712360e50061655a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (Split (← readReg TTBR1_EL2) 64)
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (Split (← readReg TTBR1_EL2) 64)
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL2_SysRegRead128_ae708511fcb38e92 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TTBR1_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) ← do (Split (← (NVMem_read__1 (BitVec.toNat 0x210#12) 128)) 64)
                              (X_set (t +i 1) 64 __tup_0)
                              (X_set t 64 __tup_1))
                          else
                            (do
                              let (__tup_0, __tup_1) ← do (Split (← (TTBR1_EL1_read ())) 64)
                              (X_set (t +i 1) 64 __tup_0)
                              (X_set t 64 __tup_1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let (__tup_0, __tup_1) ← do (Split (← readReg TTBR1_EL2) 64)
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))
                      else
                        (do
                          let (__tup_0, __tup_1) ← do (Split (← (TTBR1_EL1_read ())) 64)
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (Split (← (TTBR1_EL1_read ())) 64)
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def VTTBR_EL2_SysRegRead128_a9b3226c12a0e07e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
              let (__tup_0, __tup_1) ← do (Split (← (NVMem_read__1 (BitVec.toNat 0x020#12) 128)) 64)
              (X_set (t +i 1) 64 __tup_0)
              (X_set t 64 __tup_1))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (Split (← (VTTBR_EL2_read ())) 64)
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (Split (← (VTTBR_EL2_read ())) 64)
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def PAR_EL1_SysRegWrite128_e67f3244d494abe6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_PAR_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_PAR_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_D128En ← (( do (pure (_get_HCRX_EL2_Type_D128En (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_PAR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_D128En == 0#1)))))) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let (__tup_0, __tup_1) ← do (pure ((← (X_read (t +i 1) 64)), (← (X_read t 64))))
                          (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 127 64 __tup_0)))
                          (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 63 0 __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((← (X_read (t +i 1) 64)), (← (X_read t 64))))
                      (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 127 64 __tup_0)))
                      (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 63 0 __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((← (X_read (t +i 1) 64)), (← (X_read t 64))))
                  (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 127 64 __tup_0)))
                  (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 63 0 __tup_1))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def RCWMASK_EL1_SysRegWrite128_b8a59eaf95f35a5f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_RCWMASKEn ← (( do (pure (_get_SCR_EL3_Type_RCWMASKEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_nRCWMASK_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_nRCWMASK_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_D128En ← (( do (pure (_get_HCRX_EL2_Type_D128En (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_nRCWMASK_EL1 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_D128En == 0#1)))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                              else
                                (do
                                  let (tup__0, tup__1) ← do (pure ((← (X_read (t +i 1) 64)), (← (X_read t 64))))
                                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWMASK_EL1) 127 64 tup__0)
                                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWMASK_EL1) 63 0 tup__1))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              let (tup__0, tup__1) ← do (pure ((← (X_read (t +i 1) 64)), (← (X_read t 64))))
                              writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWMASK_EL1) 127 64 tup__0)
                              writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWMASK_EL1) 63 0 tup__1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (tup__0, tup__1) ← do (pure ((← (X_read (t +i 1) 64)), (← (X_read t 64))))
                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWMASK_EL1) 127 64 tup__0)
                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWMASK_EL1) 63 0 tup__1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def RCWSMASK_EL1_SysRegWrite128_d70b97b0479af313 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_RCWMASKEn ← (( do (pure (_get_SCR_EL3_Type_RCWMASKEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR2_EL2_nRCWSMASK_EL1 ← (( do (pure (_get_HFGWTR2_EL2_Type_nRCWSMASK_EL1 (← readReg HFGWTR2_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_D128En ← (( do (pure (_get_HCRX_EL2_Type_D128En (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HFGWTR2_EL2_nRCWSMASK_EL1 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_D128En == 0#1)))))) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                              else
                                (do
                                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                                  then
                                    (do
                                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                                  else
                                    (do
                                      let (tup__0, tup__1) ← do (pure ((← (X_read (t +i 1) 64)), (← (X_read t 64))))
                                      writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWSMASK_EL1) 127 64 tup__0)
                                      writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWSMASK_EL1) 63 0 tup__1)))))))))
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
                  if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              let (tup__0, tup__1) ← do (pure ((← (X_read (t +i 1) 64)), (← (X_read t 64))))
                              writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWSMASK_EL1) 127 64 tup__0)
                              writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWSMASK_EL1) 63 0 tup__1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (tup__0, tup__1) ← do (pure ((← (X_read (t +i 1) 64)), (← (X_read t 64))))
                  writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWSMASK_EL1) 127 64 tup__0)
                  writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange (← readReg RCWSMASK_EL1) 63 0 tup__1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_ImpDefSysRegWrite128 (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (t : Int) (t2 : Int) : SailM Unit := do
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL1_SysRegWrite128_66ee61de597f133e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TVM ← (( do (pure (_get_HCR_EL2_Type_TVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGWTR_EL2_TTBR0_EL1 ← (( do (pure (_get_HFGWTR_EL2_Type_TTBR0_EL1 (← readReg HFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_D128En ← (( do (pure (_get_HCRX_EL2_Type_D128En (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TTBR0_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_D128En == 0#1)))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                          then
                            (do
                              if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                              then (NVMem_set__1 (BitVec.toNat 0x200#12) 128 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))
                              else (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL1_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (TTBR0_EL2_write (Mk_TTBR0_EL2_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL2_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))
                      else (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL1_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL1_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL1_SysRegWrite128_8ea27f288a4b152e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (NVMem_set__1 (BitVec.toNat 0x200#12) 128 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL1_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL1_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL2_SysRegWrite128_db720477dd35bd78 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else (TTBR0_EL2_write (Mk_TTBR0_EL2_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL2_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (TTBR0_EL2_write (Mk_TTBR0_EL2_Type (Sail.BitVec.updateSubrange (← (TTBR0_EL2_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL1_SysRegWrite128_d20c29029eb4ed94 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (NVMem_set__1 (BitVec.toNat 0x210#12) 128 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR1_EL1_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR1_EL1_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL2_SysRegWrite128_4bfd1913f2c26b7d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TVM == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGWTR_EL2_TTBR1_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                          then (NVMem_set__1 (BitVec.toNat 0x210#12) 128 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))
                          else (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR1_EL1_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange (← readReg TTBR1_EL2) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))
                      else (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR1_EL1_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange (← (TTBR1_EL1_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL2_SysRegWrite128_c87556637100112b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange (← readReg TTBR1_EL2) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange (← readReg TTBR1_EL2) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def VTTBR_EL2_SysRegWrite128_3ec09d9d33270957 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_D128En ← (( do (pure (_get_SCR_EL3_Type_D128En (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (NVMem_set__1 (BitVec.toNat 0x020#12) 128 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_D128En == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else (VTTBR_EL2_write (Mk_VTTBR_EL2_Type (Sail.BitVec.updateSubrange (← (VTTBR_EL2_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (VTTBR_EL2_write (Mk_VTTBR_EL2_Type (Sail.BitVec.updateSubrange (← (VTTBR_EL2_read ())) 127 0 ((← (X_read (t +i 1) 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: el : Int, t : Int, t2 : Int -/
def AArch64_ImpDefSysInstr128 (el : Int) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (t : Int) (t2 : Int) : SailM Unit := do
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2E1IS_SysOpsWrite128_143f65c3f5ba3d9d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2E1IS_SysOpsWrite128_18df36996791819c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2E1OS_SysOpsWrite128_27f384221424e41f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2E1OS_SysOpsWrite128_db7744f725bc7991 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2E1_SysOpsWrite128_769364ab2331c0c6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2E1_SysOpsWrite128_97574c637b9ec852 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1IS_SysOpsWrite128_0a969d7a2aebccaa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1IS_SysOpsWrite128_ddc96d61f96d402c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1OS_SysOpsWrite128_84c03ae163aa7f64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1OS_SysOpsWrite128_eb8e7b685976ccc1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1_SysOpsWrite128_0213d7545787eba6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1_SysOpsWrite128_a67ad741d30f9316 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_IPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2E1IS_SysOpsWrite128_5606c3b58f00738a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2E1IS_SysOpsWrite128_f1e0663ca68347ee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2E1OS_SysOpsWrite128_65e5b4cfbd986df8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2E1OS_SysOpsWrite128_7ffb607d8c97e12e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2E1_SysOpsWrite128_00618fa8e6f5ccba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2E1_SysOpsWrite128_027f5860c67e4500 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2LE1IS_SysOpsWrite128_86e34ca39816527e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2LE1IS_SysOpsWrite128_e4198c9938d9ac42 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2LE1OS_SysOpsWrite128_1423ee9208f18247 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2LE1OS_SysOpsWrite128_cd88b450d0aae1aa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2LE1_SysOpsWrite128_2216f4b378e15ea4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (pure ())
                  else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2LE1_SysOpsWrite128_6b2d10467902cb52 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((! (← (EL2Enabled ()))) : Bool)
                      then (pure ())
                      else (AArch64_TLBIP_RIPAS2 (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAAE1IS_SysOpsWrite128_137994942d296964 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAAE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAAE1IS_SysOpsWrite128_e47a2421133341a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAAE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAAE1OS_SysOpsWrite128_4d5abc17d7bbb375 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAAE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAAE1OS_SysOpsWrite128_6de8b9b690bdbc23 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAAE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAAE1_SysOpsWrite128_2226e9154de9d452 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAAE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAAE1_SysOpsWrite128_9de89135f49c3abe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT)) <&&> (do
                         (pure (! (HaveEL EL3))) <||> (do
                           (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAAE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAALE1IS_SysOpsWrite128_216de9de0e6c2edd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAALE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAALE1IS_SysOpsWrite128_b0040cdc6216868a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAALE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAALE1OS_SysOpsWrite128_4c5726524a6ca4f1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAALE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAALE1OS_SysOpsWrite128_fb31802a92e4d6d3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAALE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAALE1_SysOpsWrite128_23742d31e3585c34 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT)) <&&> (do
                         (pure (! (HaveEL EL3))) <||> (do
                           (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAALE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAALE1_SysOpsWrite128_af1f37b9406d3bd8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAALE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE1IS_SysOpsWrite128_07c7343c7a06f43b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE1IS_SysOpsWrite128_7b5e59f759169cbe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE1OS_SysOpsWrite128_52f9177ad8036aaf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE1OS_SysOpsWrite128_953ff681e796131f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE1_SysOpsWrite128_b52389d29991d886 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT)) <&&> (do
                         (pure (! (HaveEL EL3))) <||> (do
                           (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVAE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE1_SysOpsWrite128_f48006a3d9b88992 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVAE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE2IS_SysOpsWrite128_2948c6fb18c42d37 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE2IS_SysOpsWrite128_37a80b444583dcfc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                          then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE2OS_SysOpsWrite128_056a89fd4c4c08d4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE2OS_SysOpsWrite128_e6b87760c99e44b3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                          then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE2_SysOpsWrite128_86fa76bdb392deaa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE2_SysOpsWrite128_b5df47d526785ddb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                          then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE3IS_SysOpsWrite128_46b2dc8d96c6ca59 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE3IS_SysOpsWrite128_b118fa02f013962a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE3OS_SysOpsWrite128_2d1acd5b6076c150 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE3OS_SysOpsWrite128_33932d5a554256a9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE3_SysOpsWrite128_66b8dabb6e1234b5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE3_SysOpsWrite128_c37498e172f8a592 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE1IS_SysOpsWrite128_224b4e2dae034d4f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVALE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE1IS_SysOpsWrite128_cf2c532882ecc547 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVALE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE1OS_SysOpsWrite128_1b08f32f781f6c38 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVALE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE1OS_SysOpsWrite128_61edb4ff984a675a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVALE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE1_SysOpsWrite128_1ab99e0606965efe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIRVALE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE1_SysOpsWrite128_a58a625d30647a57 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT)) <&&> (do
                         (pure (! (HaveEL EL3))) <||> (do
                           (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIRVALE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE2IS_SysOpsWrite128_6ce0d3b37f2eb132 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE2IS_SysOpsWrite128_f13b8d96621db228 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                          then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE2OS_SysOpsWrite128_4cbf07be986045b1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE2OS_SysOpsWrite128_cdc44a4c2d2759bb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                          then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE2_SysOpsWrite128_58a5be41d9a1fad2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                          then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE2_SysOpsWrite128_aba1731a5a045759 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                      then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL2)) Regime_EL2 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE3IS_SysOpsWrite128_2e388db98e6348e6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE3IS_SysOpsWrite128_46d9aa7cf0e1fea9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE3OS_SysOpsWrite128_4554dd46823f3440 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE3OS_SysOpsWrite128_49511edcb37be47c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE3_SysOpsWrite128_6d1241c816962fe5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVALE3_SysOpsWrite128_adcd898f13a55f9e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_RVA (← (SecurityStateAtEL EL3)) Regime_EL3 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAAE1IS_SysOpsWrite128_6f38dc04822d7f72 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAAE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAAE1IS_SysOpsWrite128_b3b4c6858b271cb2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAAE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAAE1OS_SysOpsWrite128_214fb682d8bbb61c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAAE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAAE1OS_SysOpsWrite128_edb83d9ce2a356a5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAAE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAAE1_SysOpsWrite128_221a9e5bd861a7fa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT)) <&&> (do
                         (pure (! (HaveEL EL3))) <||> (do
                           (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAAE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAAE1_SysOpsWrite128_b6cdb1aa6c90e3df (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAAE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1IS_SysOpsWrite128_351b0a0a4456682c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAALE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1IS_SysOpsWrite128_60f538ade9f32bfe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAALE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1OS_SysOpsWrite128_323a394d866290cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAALE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1OS_SysOpsWrite128_4c241ac6279d85ce (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAALE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1_SysOpsWrite128_9ce40ceffd0fb221 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT)) <&&> (do
                         (pure (! (HaveEL EL3))) <||> (do
                           (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAALE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1_SysOpsWrite128_ff6dfd8757e0cbb3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAALE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VAA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Last TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE1IS_SysOpsWrite128_3c8e3a9292561f7f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAE1IS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE1IS_SysOpsWrite128_642964df3a972e1f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBIS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAE1IS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE1OS_SysOpsWrite128_4fca314b90574242 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TTLBOS == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAE1OS == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE1OS_SysOpsWrite128_5f990b510a7de734 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                             (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAE1OS == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE1_SysOpsWrite128_269036cb186b79de (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (IsFeatureImplemented FEAT_FGT)) <&&> (do
                         (pure (! (HaveEL EL3))) <||> (do
                           (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                         (IsFeatureImplemented FEAT_HCX)) <&&> (do
                         (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_FGTnXS == 0#1)))))) && (__HFGITR_EL2_TLBIVAE1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE1_SysOpsWrite128_2afef2540faab1fa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_TLBIVAE1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if (((← (EL2Enabled ())) && (__HCR_EL2_FB == 1#1)) : Bool)
                  then
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
                  else
                    (do
                      if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                             (IsFeatureImplemented FEAT_HCX)) <&&> (do
                             (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2) : Bool)
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE2IS_SysOpsWrite128_def0db16c10c82b4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                          then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE2IS_SysOpsWrite128_ed37b404a865a78e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE2OS_SysOpsWrite128_9f4cafd772ff7049 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
              else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                      then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))
                      else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_AllAttr ((← (X_read t2 64)) +++ (← (X_read t 64))))))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE2OS_SysOpsWrite128_a8e74684c20ce76a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                          then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE2_SysOpsWrite128_6e51a4b4d32de64a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                  else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64)))))
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
                          then (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))
                          else (AArch64_TLBIP_VA (← (SecurityStateAtEL EL2)) Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_ExcludeXS ((← (X_read t2 64)) +++ (← (X_read t 64))))))
                  else (pure ())))))


